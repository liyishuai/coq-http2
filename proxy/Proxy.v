From HTTP2.proxy Require Import AppType.
From HTTP2.src.HPACK Require Import HPACKAbs HPACKTypes.
From HTTP2.src Require Import Types.
From HTTP2.src.Util Require Import OptionE StringUtil.
Require Import String BinNat List Bvector.
Require Import ExtLib.Data.Monads.StateMonad.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Module Proxy (codec:HPACK) : AppType codec.
  Definition Authority := string * string. (* The host and port to connect to *)
  Definition Continuation := bool. (* Whether the proxy is currently waiting for 
                                   continuation frames. *)
  Definition Compression_ctxt := DTable. 
  Definition Decompression_ctxt := DTable.
  Definition buffer := string. (* Current accumulation of headers or push_promise *)
  Definition app_state := Settings * option Authority * Continuation *
                          Compression_ctxt * Decompression_ctxt * buffer.
  Definition init : app_state -> app_state := id.
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
    let decode s app_s :=
        let '(setts, oauth, cont, cctxt, dctxt, buff) := app_s in
        match codec.decodeHeader dctxt s with
        | inl _ => (Failure "COMPRESSION_ERROR", app_s)
        | inr (hl, dctxt') =>
          let find s := SetoidList.findA (string_beq s) hl in 
          match find ":method" with
          | None => (Failure "Non connect header received", app_s)
          | Some s =>
            if string_beq s "CONNECT"
            then
              match find ":scheme", find ":path" with
              | None, None =>
                match find ":authority" with
                | None => (Failure "No authority for connect method", app_s)
                | Some s =>
                  match String_splitAtSub ":" s with
                  | None => (Failure "Authority port not seperated by colon", app_s)
                  | Some (s1, s2) =>
                    match codec.encodeHeader defaultEncodeStrategy
                                             cctxt [(":status", "200")] with
                    | inl _ => (Failure "Should be unreachable", app_s)
                    | inr (hbf, cctxt') =>
                      let fp := HeadersFrame None hbf in
                      let fh := Build_FrameHeader (framePayloadLength fp)
                                                  (toFrameFlagsField GoAwayType GoAwayFlags)
                                                  (Ndigits.N2Bv_gen 31 0) in
                      (Success (Build_Frame fh HeadersType fp),
                       (setts, Some (s1, s2), false, cctxt', dctxt', ""))
                    end
                  end
                end
              | _, _ => (Failure "scheme or path sent in connect", app_s)
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
                   | HeadersFrame _ hbf =>
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