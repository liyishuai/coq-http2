Set Warnings "-local-declaration,-scope".

From Coq Require Import Basics Bool Equality ProofIrrelevance Vector.
Import VectorNotations.

Fixpoint splitAt {A} (l : nat) {r : nat} :
  Vector.t A (l + r) -> Vector.t A l * Vector.t A r :=
  match l with
  | 0 => fun v => ([], v)
  | S l' => fun v =>
    let (v1, v2) := splitAt l' (tl v) in
    (hd v::v1, v2)
  end.

Theorem split_append {A} (l : nat) : forall {r : nat} (v : Vector.t A l) (w : Vector.t A r),
    splitAt l (append v w) = (v, w).
Proof with simpl; auto.
  induction l; intros; dependent destruction v...
  rewrite IHl...
Qed.

Open Scope program_scope.
Open Scope bool_scope.

Definition forallb {A n} (f : A -> bool) : Vector.t A n -> bool :=
  fold_left (fun x => andb x ∘ f) true.

Definition existsb {A n} (f : A -> bool) : Vector.t A n -> bool :=
  fold_left (fun x => orb x ∘ f) false.

Lemma fold_left_id {A B n} (f : B -> A -> B) (base : B) :
  (forall a : A, f base a = base) ->
  forall v : Vector.t A n,
    fold_left f base v = base.
Proof with simpl; auto.
  induction v...
  rewrite H...
Qed.

Corollary forallb_cons {A n} (f : A -> bool) (a : A) (v : Vector.t A n) :
  forallb f (a::v) = f a && forallb f v.
Proof with simpl; auto.
  intros.
  unfold forallb.
  unfold compose...
  destruct (f a)...
  apply fold_left_id...
Qed.

Corollary existsb_cons {A n} (f : A -> bool) (a : A) (v : Vector.t A n) :
  existsb f (a::v) = f a || existsb f v.
Proof with simpl; auto.
  intros.
  unfold existsb.
  unfold compose...
  destruct (f a)...
  apply fold_left_id...
Qed.

Theorem forallb_true_iff {A n} (f : A -> bool) :
  forall (v : Vector.t A n),
    forallb f v = true <-> Forall (eq true ∘ f) v.
Proof with unfold compose in *; simpl in *; auto.
  induction v; split; intros...
  - constructor.
  - rewrite forallb_cons in H.
    apply andb_prop in H.
    destruct H.
    constructor...
    apply IHv...
  - rewrite forallb_cons.
    apply andb_true_iff.
    inversion H; subst...
    apply inj_pair2 in H2; subst...
    split...
    apply IHv...
Qed.

Theorem existsb_true_iff {A n} (f : A -> bool) :
  forall (v : Vector.t A n),
    existsb f v = true <-> Exists (eq true ∘ f) v.
Proof with unfold compose in *; simpl in *; auto.
  induction v; split; intros...
  - inversion H.
  - inversion H.
  - rewrite existsb_cons in H.
    apply orb_true_iff in H.
    destruct H...
    + apply Exists_cons_hd...
    + apply Exists_cons_tl...
      apply IHv...
  - rewrite existsb_cons.
    apply orb_true_iff.
    inversion H; subst...
    apply inj_pair2 in H3; subst...
    right.
    apply IHv...
Qed.

Theorem forall_exists {A n} (f : A -> bool) :
  forall v : Vector.t A n,
    forallb f v = negb (existsb (negb ∘ f) v).
Proof with simpl; auto.
  induction v...
  unfold forallb.
  unfold existsb.
  unfold compose...
  destruct (f h)...
  repeat rewrite fold_left_id...
Qed.

Lemma fold_left_eq {A B} {n : nat} (f1 f2 : B -> A -> B) :
  (forall b a, f1 b a = f2 b a) ->
  forall (v : Vector.t A n) (b : B), fold_left f1 b v = fold_left f2 b v.
Proof with simpl; auto.
  intro.
  induction v...
  intro.
  rewrite H...
Qed.

Theorem exists_forall {A n} (f : A -> bool)
  (v : Vector.t A n) :
    existsb f v = negb (forallb (negb ∘ f) v).
Proof with simpl; auto.
  rewrite forall_exists.
  unfold existsb.
  unfold compose.
  rewrite negb_involutive.
  eapply fold_left_eq.
  intros.
  rewrite negb_involutive...
Qed.
