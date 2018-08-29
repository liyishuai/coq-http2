From Coq Require Import Ascii Bvector NArith String.
From HTTP2.Util Require Import
     ByteVector VectorUtil.
Open Scope string_scope.

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

Fixpoint Bvector_tail_cons {n:nat} (v:Bvector n) (b:bool) : Bvector (n + 1) :=
  match v with
  | [] => [b]
  |  a :: v' =>
     a :: Bvector_tail_cons v' b
  end.
