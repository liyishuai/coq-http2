From Coq Require Import Ascii NArith String Vector.
Import VectorNotations.
Open Scope string_scope.

Definition ByteVector := Vector.t ascii.
Definition ByteNil : ByteVector 0 := Vector.nil ascii.

Fixpoint to_string {n : nat} (v : ByteVector n) : string :=
  match v with
  | b::v' => String b (to_string v')
  | _ => ""
  end.

Fixpoint from_string (s : string) : ByteVector (length s) :=
  match s with
  | "" => ByteNil
  | String b s' => b::from_string s'
  end.

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

Fixpoint splitAt (l : nat) {r : nat} :
  ByteVector (l + r) -> ByteVector l * ByteVector r :=
  match l with
  | 0 => fun v => ([], v)
  | S l' => fun v =>
    let (b, v') := Vector_uncons v in
    let (v1, v2) := splitAt l' v' in
    (b::v1, v2)
  end.

Fixpoint N_of_ByteVector_rec {n : nat} (acc : N) (v : ByteVector n) : N :=
  match v with
  | [] => acc
  | b::v' => N_of_ByteVector_rec (N.shiftl acc 8 + N_of_ascii b) v'
  end.

Definition N_of_ByteVector {n : nat} : ByteVector n -> N := N_of_ByteVector_rec 0.
