Require Import HTTP2.proxy.AppType.
From ExtLib Require Export StateMonad.
From Coq Require Export String.

Module Type GenericServerType (app : AppType).
  Parameter server_state: Type.
  Parameter init_server_state: server_state.
  Definition SERVER := stateT server_state app.APP.
  
  Parameter execute: (nat * string) -> SERVER (list (nat * string)).
End GenericServerType.