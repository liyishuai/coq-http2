From HTTP2.src Require Import Types HPACK.HPACKAbs.
From HTTP2.src.Util Require Import OptionE.
From Coq Require Import String.
Require Import ExtLib.Data.Monads.StateMonad.

Module Type AppType.
  Parameter app_state : Type.
  Parameter init_app_state : app_state.

  Definition APP := state app_state.

  Parameter execute : Frame -> APP (optionE Frame).
End AppType.
