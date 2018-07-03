From Coq Require Import Vector.
Import VectorNotations.

(* Deconstruct a non-empty vector. *)
Definition Vector_uncons {A} {n : nat} (v : Vector.t A (S n)) :
  A * Vector.t A n :=
  match v in Vector.t _ Sn
        return match Sn with
               | O => unit (* unreachable *)
               | S n => _
               end
  with
  | [] => tt
  | x :: xs => (x, xs)
  end.

Fixpoint splitAt {A : Type} (l : nat) {r : nat} :
  Vector.t A (l + r) -> Vector.t A l * Vector.t A r :=
  match l with
  | 0 => fun v => ([], v)
  | S l' => fun v =>
    let (b, v') := Vector_uncons v in
    let (v1, v2) := splitAt l' v' in
    (b::v1, v2)
  end.
