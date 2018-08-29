From HTTP2 Require Import Types.
From HTTP2.HPACK Require Import HPACKAbs.
From HTTP2.Util Require Import OptionE.
From Coq Require Import String.
Require Import ExtLib.Data.Monads.StateMonad.

Module Type AppType.
  Parameter app_state : Type.
  Parameter init_app_state : app_state.

  Definition APP := state app_state.

  Parameter execute : Frame -> APP (optionE Frame).
End AppType.
