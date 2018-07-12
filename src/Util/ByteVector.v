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

Fixpoint ByteVector_of_N {m : nat} (n:N) : ByteVector m :=
  match m with
  | O => ByteNil
  | S m' =>
    let x := N.shiftr_nat n (m' * 8) in
    cons ascii (ascii_of_N x) m' (ByteVector_of_N n)
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

Lemma ascii_mod_256 : forall n, ascii_of_N n = ascii_of_N (N.modulo n 256).
Proof. Admitted.

Lemma ByteVector_of_N_upper : forall x m n,
    @ByteVector_of_N n (x * 2 ^ (N.of_nat (n * 8)) + m) = @ByteVector_of_N n m.
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
                              (Pos.succ (Pos.of_succ_nat (n * 8))))))))) = 2 ^ (N.of_nat (8 + n * 8))).
  auto. repeat rewrite H; clear H.
  repeat rewrite <- Nshiftr_equiv_nat.
  repeat rewrite N.shiftr_div_pow2.
  repeat rewrite Nat2N.inj_add.
  repeat rewrite N.pow_add_r.
  rewrite N.mul_assoc. rewrite IHn.
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
  
Lemma ByteVector_of_N_embedding :
  forall n (v : ByteVector n),
    ByteVector_of_N (N_of_ByteVector v) = v.
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