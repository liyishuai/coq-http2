From HTTP2.Proxy Require Import AppType.
From HTTP2.HPACK Require Import HPACKAbs HPACKImpl HPACKTypes.
From HTTP2 Require Import Types.
From HTTP2.Util Require Import OptionE StringUtil BitField.
Require Import String BinNat List Bvector.
Require Import ExtLib.Data.Monads.StateMonad.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Module Proxy : AppType.
  Definition Authority := string * string. (* The host and port to connect to *)
  Definition Continuation := bool. (* Whether the proxy is currently waiting for
                                   continuation frames. *)
  Definition Compression_ctxt := DTable.
  Definition Decompression_ctxt := DTable.
  Definition buffer := string. (* Current accumulation of headers or push_promise *)
  Definition app_state := Settings * option Authority * Continuation *
                          Compression_ctxt * Decompression_ctxt * buffer.
  Definition init_app_state : app_state :=
        (defaultSettings, None, false, defaultDTable, defaultDTable, "").
  Definition APP := state app_state.
  (* Things to handle:
     1. No authority yet, and continuation is not set. Proxy is waiting for a
        host and port, so it should only be receiving a headers frame. Once it
        does, either the END_HEADERS flag is set and the proxy decodes the hbf
        right away, handling it as in 2, or the hbf is added to the buffer and
        continuation is set.

     2. No Authority yet, and Continuation is set. The proxy should only receive
        continuation frames until a continuation frame with END_HEADERS set is
        received. For each such continuation frame, the contents are appended to
        the buffer. Once the END_HEADERS continuation is received, the buffer is
        decoded and it must conform to the connection instructions:
        https://http2.github.io/http2-spec/#CONNECT

     3. Authority is already set. Then the proxy is forwarding frames to the
        host and port stored in app_state. WINDOW_UPDATE frames are not
        forwarded, so these must be handled. Settings frames are forwarded, but
        also processed? *)
  Definition execute (f:Frame) : APP (optionE Frame) :=
    (* Form a goaway frame for connection errors *)
    let goaway lsid e :=
        let fp := GoAwayFrame lsid e "" in
        let fh := Build_FrameHeader (framePayloadLength fp)
                                    (toFrameFlagsField GoAwayType GoAwayFlags)
                                    (Ndigits.N2Bv_gen 31 0) in
        Build_Frame fh GoAwayType fp in
    (* Form an rst frame for stream errors *)
    let rst sid e :=
        let fp := RSTStreamFrame e in
        let fh := Build_FrameHeader (framePayloadLength fp)
                                    (toFrameFlagsField RSTStreamType RSTStreamFlags)
                                    sid in
        Build_Frame fh RSTStreamType fp in
    (* Helper function that handles when the full encoded header block is received.
       The proxy expects a connect method, see
       https://http2.github.io/http2-spec/#CONNECT *)
    let decode s app_s :=
        let '(setts, oauth, cont, cctxt, dctxt, buff) := app_s in
        (* s is ready to be decoded. The spec says decoding errors MUST be treated
           as a COMPRESSION_ERROR: https://http2.github.io/http2-spec/#HeaderBlock *)
        match HPACKImpl.decodeHeader dctxt s with
        | inl _ => (Success (goaway (streamId (frameHeader f)) CompressionError), app_s)
        | inr (hl, dctxt') =>
          (* hl is the decoded header list received by the proxy *)
          let find s := SetoidList.findA (string_beq s) hl in
          (* According to https://http2.github.io/http2-spec/#CONNECT the :method
             pseudo header is set to connect *)
          match find ":method" with
          | None => (Failure "Non connect header received", app_s)
          | Some s =>
            if string_beq s "CONNECT"
            then
              (* Malformed connect requests are treated as a stream error.
                 An RST stream frame is sent including a PROTOCOL_ERROR *)
              (* According to https://http2.github.io/http2-spec/#CONNECT the
                 :scheme and :path pseudo headers MUST be omitted *)
              match find ":scheme", find ":path" with
              | None, None =>
                (* According to https://http2.github.io/http2-spec/#CONNECT the
                   :authority pseudo header contains the host and port to connect
                   to, host seperated from port by colon *)
                match find ":authority" with
                | None => (Success (rst (streamId (frameHeader f)) ProtocolError), app_s)
                | Some s =>
                  match String_splitAtSub ":" s with
                  | None => (Success (rst (streamId (frameHeader f)) ProtocolError), app_s)
                  | Some (s1, s2) =>
                    (* Once this connection is successfully established, the
                       proxy sends a HEADERS frame containing a 2xx series status
                       code to the client *)
                    match HPACKImpl.encodeHeader defaultEncodeStrategy
                                             cctxt [(":status", "200")] with
                    | inl _ => (Failure "Should be unreachable", app_s)
                    | inr (hbf, cctxt') =>
                      let fp := HeadersFrame None hbf "" in
                      let fh := Build_FrameHeader (framePayloadLength fp)
                                                  (toFrameFlagsField
                                                     HeadersType
                                                     (HeadersFlags
                                                        Bit0 Bit1 Bit0 Bit0))
                                                  (streamId (frameHeader f)) in
                      (Success (Build_Frame fh HeadersType fp),
                       (setts, Some (s1, s2), false, cctxt', dctxt', ""))
                    end
                  end
                end
              | _, _ => (Success (rst (streamId (frameHeader f)) ProtocolError), app_s)
              end
            else (Failure "Non connect method received", app_s)
          end
        end in
    mkState (fun app_s:app_state =>
               let '(setts, oauth, cont, cctxt, dctxt, buff) := app_s in
               match oauth with
               | None => (* No authority, 1,2 *)
                 if cont
                 then (* Continuation is set, 2 *)
                   match framePayload f with
                   | ContinuationFrame hbf =>
                     let flags := flags (frameHeader f) in
                     if testEndHeaders flags
                     then (* No more continuation expected. Decode here *)
                       decode (buff ++ hbf)%string app_s
                     else (* Continuation expected, add hbf to buffer and set cont *)
                       (Failure "Not sure what to do here. Is it acknowledged somehow?",
                        (setts, oauth, true, cctxt, dctxt, (buff ++ hbf)%string))
                   | _ => (Failure "Expecting continuation, other frame received", app_s)
                   end
                 else (* Continuation is not set, 1*)
                   match framePayload f with
                   | HeadersFrame _ hbf _ =>
                     let flags := flags (frameHeader f) in
                     if testEndHeaders flags
                     then (* No continuation expected. Decode right away *)
                       decode hbf app_s
                     else (* Continuation expected, add hbf to buffer and set cont *)
                       (Failure "Not sure what to do here. Is it acknowledged somehow?",
                        (setts, oauth, true, cctxt, dctxt, hbf))
                   | _ => (Failure "Expecting connect, non header frame received", app_s)
                   end
               | Some (host, port) => (* Authority is already set, 3 *)
                 let g := f in (* Modify frame to forward to host,port *)
                 (Success g, app_s)
               end).
End Proxy.
