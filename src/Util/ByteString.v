From Coq Require Import Ascii Bvector Nat String.
Open Scope string_scope.

Fixpoint pack {n : nat} (v : Bvector n) : string :=
  match v with
  | b0::b1::b2::b3::b4::b5::b6::b7::v' =>
    String (Ascii b0 b1 b2 b3 b4 b5 b6 b7) (pack v')
  | _ => ""
  end.

(* Need for help: Coq cannot guess decreasing argument of fix.
Fixpoint unpack (s : string) (n : nat) : Bvector n :=
  match s,n with
  | _, 0 => Bnil
  | String (Ascii b0 b1 b2 b3 b4 b5 b6 b7) s', S(S(S(S(S(S(S(S n'))))))) =>
    b0::b1::b2::b3::b4::b5::b6::b7::unpack s' n'
  | _, S n' =>
    false::unpack "" n'
  end.
 *)
