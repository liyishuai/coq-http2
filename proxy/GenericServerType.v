From HTTP2 Require Import proxy.AppType src.HPACK.HPACKAbs src.Types.
From ExtLib Require Export StateMonad.
From Coq Require Export String.

Definition ConnectionId := nat.

Module Type GenericServerType (app : AppType).
  Parameter server_state: Type.
  Parameter init_server_state: server_state.
  Definition SERVER := stateT server_state app.APP.
  
  Parameter execute: (ConnectionId * string) -> SERVER (list (ConnectionId * string)).
End GenericServerType.