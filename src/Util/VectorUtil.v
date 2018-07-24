Set Warnings "-local-declaration,-scope".

From Coq Require Import Equality Vector.
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

Fixpoint splitAt {A} (l : nat) {r : nat} :
  Vector.t A (l + r) -> Vector.t A l * Vector.t A r :=
  match l with
  | 0 => fun v => ([], v)
  | S l' => fun v =>
    let (b, v') := Vector_uncons v in
    let (v1, v2) := splitAt l' v' in
    (b::v1, v2)
  end.

Theorem split_append {A} (l : nat) : forall {r : nat} (v : Vector.t A l) (w : Vector.t A r),
    splitAt l (append v w) = (v, w).
Proof with simpl; auto.
  induction l; intros...
  - dependent destruction v...
  - dependent destruction v...
    rewrite IHl...
Qed.
