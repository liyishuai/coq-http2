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

(* Non exhaustive pattern-matching: no clause found for patterns S _, [] *)
(* Fixpoint splitAt (l : nat) {r : nat} (v : ByteVector (l + r)) : *)
(*   ByteVector l * ByteVector r := *)
(*   match l, v with *)
(*   | 0, _ => ([], v) *)
(*   | S l', b::v' => let (v1, v2) := splitAt l' v' in *)
(*                   (b::v1, v2) *)
(*   end. *)

Fixpoint N_of_ByteVector_rec {n : nat} (acc : N) (v : ByteVector n) : N :=
  match v with
  | [] => acc
  | b::v' => N_of_ByteVector_rec (N.shiftl acc 8 + N_of_ascii b) v'
  end.

Definition N_of_ByteVector {n : nat} : ByteVector n -> N := N_of_ByteVector_rec 0.
