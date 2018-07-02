From Coq Require Import Ascii Bvector Nat String.
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
