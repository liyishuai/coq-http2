From HTTP2.proxy Require Import AppType.
From HTTP2.src.HPACK Require Import HPACKAbs.
From HTTP2.src Require Import Types Util.OptionE.
Require Import String BinNat.
Require Import ExtLib.Data.Monads.StateMonad.

Module Proxy (codec:HPACK) : AppType codec.
  Definition Authority := string * N. (* The host and port to connect to *)
  Definition app_state := Settings * option Authority.
  Definition init : app_state -> app_state := id.
  Definition init_app_state : app_state := (defaultSettings, None).
  Definition APP := state app_state.
  Definition execute (f:Frame) : APP (optionE Frame) :=
    mkState (fun app_s => (Failure "unimplemented", app_s)).
End Proxy.