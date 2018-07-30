From Coq Require Import Ascii Basics NArith String Vector.
Import VectorNotations.
Open Scope program_scope.
Open Scope string_scope.
Open Scope N_scope.

Definition ByteVector := Vector.t ascii.
Definition ByteNil : ByteVector 0 := Vector.nil ascii.

Definition to_string {n : nat} : ByteVector n -> string :=
  (fun v => fold_right String v "") ∘ rev.

Fixpoint from_string' (s : string) : ByteVector (length s) :=
  match s with
  | "" => ByteNil
  | String b s' => b::from_string' s'
  end.

Definition from_string (s : string) : ByteVector (length s) :=
  rev (from_string' s).

Fixpoint N_of_ByteVector {n : nat} (v : ByteVector n) : N :=
  match v with
  | [] => 0
  | a::v' =>
    N_of_ascii a + N_of_ByteVector v' * 256
  end.

Fixpoint ByteVector_of_N (m : nat) (n:N) : ByteVector m :=
  match m with
  | O => ByteNil
  | S m' =>
    ascii_of_N n::ByteVector_of_N m' (N.shiftr n 8)
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
Proof with auto.
  induction v; simpl...
  - constructor.
  - apply N.le_lt_trans with (255 + 256 * N_of_ByteVector v).
    rewrite N.mul_comm.
    apply N.add_le_mono_r with (n := N_of_ascii h).
    apply ascii_upperbound.
    repeat rewrite <- Nshiftl_equiv_nat in *.
    repeat rewrite N.shiftl_mul_pow2 in *.
    repeat rewrite N.double_mul.
    replace (N.double (N.double (N.double (N.double (N.double (N.double (N.double (N.double 1)))))))) with (1 + 255)...
    apply N.lt_le_trans with (m := 256 * 1 + 256 * (N_of_ByteVector v)).
    apply N.add_lt_mono_r.
    constructor.
    rewrite <- N.mul_add_distr_l.
    apply N.mul_le_mono_l.
    apply N.lt_pred_le.
    rewrite N.add_1_l.
    rewrite N.pred_succ.
    rewrite <- N.mul_1_l...
Qed.

Lemma pow_lower : forall n m, n <> 0 -> n ^ m <> 0.
Proof.
  intros. destruct m. simpl; discriminate.
  apply (N.pow_nonzero n (N.pos p)) in H; auto.
Qed.

Lemma add_pow2 : forall n m x,
      n < 2 ^ m -> (x * 2 ^ m + n) / 2 ^ m = x.
Proof.
  intros. rewrite N.div_add_l.
  rewrite N.div_small; auto. rewrite N.add_0_r; auto.
  apply pow_lower; discriminate.
Qed.

Lemma pos_mod_1 : forall p n,
    N.pos (xI p) mod (2 ^ n) = N.pos p mod (2 ^ (n - 1)) + 2 ^ (n - 1).
Proof. Admitted.

Lemma pos_mod_0 : forall p n,
    N.pos (xO p) mod (2 ^ n) = N.pos p mod (2 ^ (n - 1)).
Proof. Admitted.


Lemma pos_shiftr_1 : forall p,
    N.shiftr (N.pos (xI p)) 1 = N.pos p.
Proof.
  trivial. Qed.

Lemma pos_shiftr_0 : forall p,
    N.shiftr (N.pos (xO p)) 1 = N.pos p.
Proof.
  trivial. Qed.

Lemma shiftr_succ : forall n m,
    N.shiftr n (N.succ m) = N.shiftr (N.shiftr n m) 1.
Proof.
  intros.
  rewrite <- N.add_1_r. rewrite N.shiftr_shiftr. auto.
Qed.

Lemma ascii_mod_256 : forall n, ascii_of_N n = ascii_of_N (N.modulo n 256).
Proof.
  intros. unfold ascii_of_N. destruct n; auto.
  assert (256 = 2^8); auto. rewrite H.
  destruct p; try destruct p; try destruct p; try destruct p; try destruct p;
    try destruct p; try destruct p; try destruct p; auto.
  - rewrite N.mod_eq. rewrite <- N.shiftr_div_pow2.
    assert (8 = N.succ (N.succ (N.succ (N.succ (N.succ (N.succ (N.succ (N.succ 0))))))));
      auto. rewrite H0. repeat rewrite N.shiftr_shiftr. repeat rewrite shiftr_succ.
    rewrite N.shiftr_0_r. repeat rewrite pos_shiftr_1. rewrite <- H0.
    cut (N.pos p~1~1~1~1~1~1~1~1 - 2 ^ 8 * N.pos p =
            255).
    + intros. rewrite H1. reflexivity.
    + apply (Pos.peano_ind (fun p => N.pos p~1~1~1~1~1~1~1~1 - 2 ^ 8 * N.pos p = 255));
        auto; intros.
    Admitted.

Lemma ByteVector_of_N_upper : forall x m n,
    ByteVector_of_N n (x * 2 ^ (N.of_nat (n * 8)) + m) = ByteVector_of_N n m.
(*
Proof.
  intros. generalize dependent x. induction n; auto. intros.
  simpl.
  assert (N.pos
          (2 ^ Pos.succ
               (Pos.succ
                  (Pos.succ
                     (Pos.succ
                        (Pos.succ
                           (Pos.succ
                              (Pos.succ (Pos.of_succ_nat (n * 8))))))))) = 2 ^ (N.of_nat (8 + n * 8)));
    auto; repeat rewrite H; clear H.
  repeat rewrite <- Nshiftr_equiv_nat.
  repeat rewrite N.shiftr_div_pow2.
  repeat rewrite Nat2N.inj_add.
  repeat rewrite N.pow_add_r.
  rewrite N.mul_assoc.
  rewrite IHn.
  rewrite ascii_mod_256.
  assert ((((x * 2 ^ N.of_nat 8 * 2 ^ N.of_nat (n * 8) + m) /
      2 ^ N.of_nat (n * 8)) mod 256) = (m / 2 ^ N.of_nat (n * 8)) mod 256).
  { rewrite N.div_add_l. rewrite <- N.add_mod_idemp_l; try discriminate.
    assert ((x * 2 ^ N.of_nat 8) mod 256 = 0).
    { assert (2 ^ N.of_nat 8 = 256); auto.
      rewrite H; clear H. rewrite N.mod_mul; auto; discriminate. }
    rewrite H. rewrite N.add_0_l; auto.
    apply pow_lower; discriminate. }
  rewrite H. rewrite <- ascii_mod_256; auto.
Qed.
*) Admitted.

Lemma ByteVector_of_N_embedding :
  forall n (v : ByteVector n),
    ByteVector_of_N n (N_of_ByteVector v) = v.
(*
Proof.
  intros. induction v; auto; simpl.
  pose proof ByteVector_upperbound n v.
  repeat rewrite <- Nshiftl_equiv_nat in *.
  repeat rewrite <- Nshiftr_equiv_nat.
  repeat rewrite N.shiftl_mul_pow2 in *.
  repeat rewrite N.shiftr_div_pow2.
  rewrite N.mul_1_l in H.
  rewrite add_pow2; auto. rewrite ascii_N_embedding.
  rewrite ByteVector_of_N_upper. rewrite IHv; auto.
Qed.
*) Admitted.
