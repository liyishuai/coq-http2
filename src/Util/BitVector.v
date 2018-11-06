From Coq Require Import Ascii Basics Bvector ByteVector NArith String Vector.
From HTTP2.Util Require Import
     VectorUtil StringUtil.
Open Scope string_scope.
Open Scope program_scope.

Program Fixpoint Bvector_tail_cons {n:nat} (v:Bvector n) (b:bool) : Bvector (n + 1) :=
  shiftin b v.
Solve Obligations with intros; rewrite PeanoNat.Nat.add_1_r; reflexivity.

Fixpoint hex_of_Bvector_ {n : nat} (v : Bvector n) (acc : string) :
  string :=
  match v with
  | b0 :: b1 :: b2 :: b3 :: v' =>
    hex_of_Bvector_ v' (hex b0 b1 b2 b3 ::: acc)
  | b0 :: b1 :: b2 :: [] => hex b0 b1 b2 false ::: acc
  | b0 :: b1 :: [] => hex b0 b1 false false ::: acc
  | b0 :: [] => hex b0 false false false ::: acc
  | [] => acc
  end.

Definition hex_of_Bvector {n : nat} (v : Bvector n) : string :=
  hex_of_Bvector_ v "".
