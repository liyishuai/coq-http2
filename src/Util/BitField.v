From Coq Require Import Bvector.

(* A bit indexed by its position in a bitfield.
   Usable as a boolean. *)
Inductive Bit (b : nat) : Type := Bit1 | Bit0.

Arguments Bit0 {b}.
Arguments Bit1 {b}.

Definition coerceBit (n m : nat) (b : Bit n) : Bit m :=
  match b with
  | Bit0 => Bit0
  | Bit1 => Bit1
  end.

Fixpoint BVnth {m : nat} (n : nat) (v : Bvector m) : bool :=
  match v, n with
  | [], _ => false
  | b :: _, O => b
  | _ :: v, S n => BVnth n v
  end.

Definition toBit {m n : nat} (v : Bvector m) : Bit n :=
  if BVnth n v then Bit1 else Bit0.

Fixpoint BVsingleton (m n : nat) : Bvector m :=
  match m, n with
  | O, _ => []
  | S _, O   => true :: Bvect_false _
  | S _, S n => false :: BVsingleton _ n
  end.

Fixpoint fromBit {m n : nat} (b : Bit n) : Bvector m :=
  match b with
  | Bit0 => Bvect_false _
  | Bit1 => BVsingleton m n
  end.
