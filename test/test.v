From HTTP2 Require Import Encode Types Util.BitField Util.BitVector.
From Coq Require Import Bvector List String Strings.Ascii.
Open Scope list_scope.

(* Http2 sample dump:
   https://wiki.wireshark.org/HTTP2 *)

Program Definition fh : FrameHeader :=
  Build_FrameHeader 4 (Bvect_false 8) 3.
Obligation 1. reflexivity. Qed.

Definition fp : FramePayload WindowUpdateType :=
  WindowUpdateFrame 32767.

Definition f : Frame := Build_Frame fh WindowUpdateType fp.

Fixpoint string_to_ascii_list s : list ascii :=
  match s with
  | EmptyString => nil%list
  | String a tl => a :: string_to_ascii_list tl
  end.

Definition string_to_N_list s := List.map N_of_ascii (string_to_ascii_list s).

Compute encodeFrameHeader f.
Compute encodePayload None f.