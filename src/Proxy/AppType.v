From HTTP2 Require Import Types.
From HTTP2.HPACK Require Import HPACKAbs.
From HTTP2.Util Require Import OptionE.
From Coq Require Import String.
Require Import ExtLib.Data.Monads.StateMonad.

(*! Section ApplicationInterface *)

(** The [AppType] module type represents the "application-level
    functionality" of a web server.  An application takes parsed HTTP
    Frames and returns HTTP Frames. It runs in a state monad, which 
    in particular includes the state of the operating system. *)
Module Type AppType.
  Parameter app_state : Type.
  Parameter init_app_state : app_state.

  (** [state] is the usual state monad, defined in the CoqExtlib
      library. *)
  Definition APP := state app_state.

  (** The [execute] operation is the core of an application. It is an
      atomic operation that takes in a parsed HTTP Frame, and
      returns an HTTP Frame, possibly also updating its internal state. *)
  Parameter execute : Frame -> APP (optionE Frame).
End AppType.
