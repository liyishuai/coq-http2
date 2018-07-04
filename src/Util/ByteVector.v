From Coq Require Import Ascii NArith String Vector.
Import VectorNotations.
Open Scope string_scope.
Open Scope N_scope.

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

Fixpoint N_of_ByteVector {n : nat} (v : ByteVector n) : N :=
  match v with
  | [] => 0
  | a::v' =>
    match n with
    | O => 0                     (* unreachable *)
    | S n' => N.shiftl_nat (N_of_ascii a) (n' * 8) + N_of_ByteVector v'
    end
  end.

Lemma ascii_upperbound' (a : ascii) : N_of_ascii a < 256.
Proof with simpl; constructor.
  destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0;
  destruct b1;
  destruct b2;
  destruct b3;
  destruct b4;
  destruct b5;
  destruct b6;
  destruct b7...
Qed.

Corollary ascii_upperbound (a : ascii) : N_of_ascii a <= 255.
Proof with auto.
  replace 255 with (N.pred 256)...
  apply N.lt_le_pred.
  apply ascii_upperbound'.
Qed.

Lemma ByteVector_upperbound : forall (n : nat) (v : ByteVector n), N_of_ByteVector v < N.shiftl_nat 1 (n * 8).
Proof with simpl; auto.
  induction v...
  - constructor.
  - repeat rewrite <- Nshiftl_equiv_nat in *.
    repeat rewrite N.shiftl_mul_pow2 in *.
    repeat rewrite N.double_mul.
    replace (N.double (N.double (N.double (N.double (N.double (N.double (N.double (N.double 1)))))))) with (255 + 1).
    + apply N.le_lt_trans with (m := 255 * 2 ^ N.of_nat (n * 8) + N_of_ByteVector v).
      * apply N.add_le_mono_r.
        apply N.mul_le_mono_r.
        apply ascii_upperbound.
      * rewrite N.mul_add_distr_r.
        apply N.add_lt_mono_l...
    + reflexivity.
Qed.
