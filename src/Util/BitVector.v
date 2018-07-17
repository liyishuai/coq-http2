From Coq Require Import Ascii Bvector NArith String.
From HTTP2 Require Import Util.ByteVector Util.VectorUtil.
Open Scope string_scope.

Fixpoint pack {n : nat} (v : Bvector n) : string :=
  match v with
  | b0::b1::b2::b3::b4::b5::b6::b7::v' =>
    String (Ascii b0 b1 b2 b3 b4 b5 b6 b7) (pack v')
  | _ => ""
  end.

Fixpoint unpack (s : string) : Bvector (length s * 8) :=
  match s with
  | EmptyString => Bnil
  | String (Ascii b0 b1 b2 b3 b4 b5 b6 b7) s' =>
    b0::b1::b2::b3::b4::b5::b6::b7::unpack s'
  end.

Fixpoint Bvector_of_ByteVector {n : nat} (v : ByteVector n) : Bvector (n * 8) :=
  match v with
  | [] => []
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7::v' =>
    b0::b1::b2::b3::b4::b5::b6::b7::Bvector_of_ByteVector v'
  end.

Fixpoint ByteVector_of_Bvector {n : nat} : Bvector (n * 8) -> ByteVector n :=
  match n with
  | O => fun _ => []
  | S n' =>
    fun v =>
      let (b0, v1) := Vector_uncons v in
      let (b1, v2) := Vector_uncons v1 in
      let (b2, v3) := Vector_uncons v2 in
      let (b3, v4) := Vector_uncons v3 in
      let (b4, v5) := Vector_uncons v4 in
      let (b5, v6) := Vector_uncons v5 in
      let (b6, v7) := Vector_uncons v6 in
      let (b7, v8) := Vector_uncons v7 in
      Ascii b0 b1 b2 b3 b4 b5 b6 b7::ByteVector_of_Bvector v8
  end.

Fixpoint N_of_Bvector_rec {n : nat} (acc : N) (v : Bvector n) : N :=
  match v with
  | [] => acc
  | b::v' => N_of_Bvector_rec ((if b then N.succ_double else N.double) acc) v'
  end.

Definition N_of_Bvector {n : nat} : Bvector n -> N := N_of_Bvector_rec 0.
