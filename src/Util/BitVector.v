From Coq Require Import Ascii Bvector NArith String.
From HTTP2 Require Import Util.ByteVector Util.VectorUtil.
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

(* https://github.com/coq/coq/pull/8169 *)
Fixpoint P2Bv_sized (m : nat) (p : positive) : Bvector m :=
  match m with
  | O => []
  | S m =>
    match p with
    | xI p => true  :: P2Bv_sized  m p
    | xO p => false :: P2Bv_sized  m p
    | xH   => true  :: Bvect_false m
    end
  end.

Definition N2Bv_sized (m : nat) (n : N) : Bvector m :=
  match n with
  | N0     => Bvect_false m
  | Npos p => P2Bv_sized  m p
  end.

Lemma N2Bv_sized_Nsize (n : N) :
  N2Bv_sized (N.size_nat n) n = N2Bv n.
Proof with simpl; auto.
  destruct n...
  induction p...
  all: rewrite IHp...
Qed.

Lemma N2Bv_sized_Bv2N (n : nat) (v : Bvector n) :
  N2Bv_sized n (Bv2N n v) = v.
Proof with simpl; auto.
  induction v...
  destruct h;
  unfold N2Bv_sized;
  destruct (Bv2N n v) as [|[]];
  rewrite <- IHv...
Qed.
