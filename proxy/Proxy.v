From HTTP2.proxy Require Import AppType.
From HTTP2.src.HPACK Require Import HPACKAbs HPACKTypes.
From HTTP2.src Require Import Types Util.OptionE.
Require Import String BinNat.
Require Import ExtLib.Data.Monads.StateMonad.
Open Scope string_scope.

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
                       let s := buff ++ hbf in
                       (Failure "Unimplemented", app_s)
                     else (* Continuation expected, add hbf to buffer and set cont *)
                       (Failure "Not sure what to do here. Is it acknowledged somehow?",
                        (setts, oauth, true, cctxt, dctxt, buff ++ hbf))
                   | _ => (Failure "Expecting continuation, other frame received", app_s)
                   end
                 else (* Continuation is not set, 1*)
                   match framePayload f with
                   | HeadersFrame _ hbf =>
                     let flags := flags (frameHeader f) in
                     if testEndHeaders flags
                     then (* No continuation expected. Decode right away *)
                       (Failure "Unimplemented", app_s)
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