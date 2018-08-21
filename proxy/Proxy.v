From HTTP2.proxy Require Import AppType.
From HTTP2.src.HPACK Require Import HPACKAbs HPACKTypes.
From HTTP2.src Require Import Types Util.OptionE.
Require Import String BinNat.
Require Import ExtLib.Data.Monads.StateMonad.
Open Scope string_scope.

Module Proxy (codec:HPACK) : AppType codec.
  Definition Authority := string * N. (* The host and port to connect to *)
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
     1. No Authority yet, and Continuation is set. The proxy should only receive 
        continuation frames until a continuation frame with END_HEADERS set is 
        received. For each such continuation frame, the contents are appended to
        the buffer. Once the END_HEADERS continuation is sent, the buffer is 
        decoded and processed according to points below, and Continuation is set
        to false.

     2. No authority yet. Proxy is waiting for a host and port, so it should 
        only be receiving a headers or continuation frame. Once the END_HEADERS
        continuation is received, the decoded buffer must conform to the 
        connection instructions: https://http2.github.io/http2-spec/#CONNECT

     3. Authority is already set. Then the proxy is forwarding frames to the 
        host and port stored in app_state. WINDOW_UPDATE frames are not 
        forwarded, so these must be handled. Settings frames are forwarded, but
        also processed? *)
  Definition execute (f:Frame) : APP (optionE Frame) :=
    mkState (fun app_s =>
               let '(setts, oauth, cont, cctxt, dctxt, buff) := app_s in
               ((Failure "Unimplemented"), app_s)).
End Proxy.