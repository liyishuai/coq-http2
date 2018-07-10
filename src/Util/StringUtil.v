From Coq Require Import String.
Open Scope string_scope.

Fixpoint String_splitAt (n : nat) (s : string) : option (string * string) :=
  match n, s with
  | 0, _ => Some ("", s)
  | S _, "" => None
  | S n', String a s' =>
    match String_splitAt n' s' with
    | Some (s1, s2) => Some (String a s1, s2)
    | None => None
    end
  end.

Lemma String_splitAt_lengthSome (n : nat) (s : string) :
  n <= length s <->
  exists s1 s2, String_splitAt n s = Some (s1, s2).
Proof with simpl in *; subst; eauto.
  split; generalize dependent n; induction s; intros...
  - inversion H...
  - destruct n...
    apply le_S_n in H.
    apply IHs in H.
    destruct H.
    destruct H.
    rewrite H...
  - destruct n...
    destruct H.
    destruct H.
    inversion H.
  - destruct n...
    + apply le_0_n.
    + apply le_n_S.
      apply IHs.
      destruct H.
      destruct H.
      destruct (String_splitAt n s)...
      destruct p...
Qed.

Lemma String_splitAt_lengthFst : forall (s s1 s2: string) (n : nat),
    String_splitAt n s = Some (s1, s2) ->
    length s1 = n.
Proof with simpl in *; subst; eauto.
  induction s; intros; destruct n; try inversion H...
  destruct (String_splitAt n s) eqn:Heq...
  - destruct p.
    inversion H...
  - inversion H.
Qed.

Lemma String_splitAt_Some : forall (s s1 s2 : string) (n : nat),
    String_splitAt n s = Some (s1, s2) ->
    s = s1 ++ s2.
Proof with simpl in *; subst; eauto.
  induction s; intros; destruct n; try inversion H...
  destruct (String_splitAt n s) eqn:Heq...
  - destruct p.
    inversion H...
    erewrite IHs...
  - inversion H.
Qed.

Lemma String_splitAt_None (n : nat) (s : string) :
  length s < n <-> String_splitAt n s = None.
Proof with simpl in *; subst; auto.
  split.
  - generalize dependent n.
    induction s...
    + destruct n...
      intros.
      inversion H.
    + intros.
      destruct n...
      * inversion H.
      * apply Lt.lt_S_n in H.
        apply IHs in H.
        rewrite H...
  - generalize dependent n.
    induction s...
    + destruct n...
      * intros.
        inversion H.
      * intros.
        apply PeanoNat.Nat.lt_0_succ.
    + destruct n...
      * intros.
        inversion H.
      * destruct (String_splitAt n s) eqn:Hsplit.
        ** destruct p...
           intros.
           inversion H.
        ** intros.
           apply Lt.lt_n_S...
Qed.
