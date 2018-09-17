From Coq Require Import Ascii Bvector NArith String.
From HTTP2.Util Require Import
     ByteVector VectorUtil StringUtil.
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

Fixpoint Bvector_of_N {n : nat} (m : N) : Bvector n :=
  match n with
  | O => []
  | S n' =>
    match m with
    | N0 => false :: Bvector_of_N m
    | Npos p =>
      match p with
      | xI p' => true  :: Bvector_of_N (Npos p')
      | xO p' => false :: Bvector_of_N (Npos p')
      | xH => true :: Bvector_of_N N0
      end
    end
  end.

Fixpoint N_of_Bvector {n : nat} (v : Bvector n) : N :=
  match v with
  | [] => 0
  | b :: v' =>
    let m' := N_of_Bvector v' in
    if b then 1 + 2 * m' else 2 * m'
  end.

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
