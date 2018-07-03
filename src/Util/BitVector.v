From Coq Require Import Ascii Bvector NArith String.
From HTTP2 Require Import Util.ByteVector.
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

Fixpoint N_of_Bvector_rec {n : nat} (acc : N) (v : Bvector n) : N :=
  match v with
  | [] => acc
  | b::v' => N_of_Bvector_rec ((if b then N.succ_double else N.double) acc) v'
  end.

Definition N_of_Bvector {n : nat} : Bvector n -> N := N_of_Bvector_rec 0.
