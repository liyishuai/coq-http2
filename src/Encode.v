From HTTP2 Require Import Types.
From Coq Require Import BinNat.
From Coq Require Import String.
Open Scope N_scope.
Open Scope string_scope.

Definition EncodeInfo :=
  (FrameFlagsField * StreamId * option N)%type.

(* https://http2.github.io/http2-spec/index.html#rfc.section.4.1 *)
Definition encodeFrameHeader (f:Frame) : string :=
  let fh := frameHeader f in
  let len := payloadLength fh in
  let ft := frameType f in
  let flgs := flags fh in
  let R := "0" in
  let si := streamId fh in
  "".
