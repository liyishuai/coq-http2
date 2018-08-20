From HTTP2.src Require Import Types HPACK.HPACKAbs.
From HTTP2.src.Util Require Import OptionE.
From Coq Require Import String.
Require Import ExtLib.Data.Monads.StateMonad.

Module Type AppType (codec:HPACK).
  Parameter app_state : Type.
  Parameter init : app_state -> app_state.
  Parameter init_app_state : app_state.

  Definition APP := state app_state.

  Parameter execute : string -> APP (optionE string).
End AppType.
