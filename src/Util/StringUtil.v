(* Rename [ascii] and [string] to [byte] and [bytes].
   This really should be [BytesUtil]. *)

From Coq Require Export
     Ascii String.
Open Scope string_scope.

Notation bit := bool (only parsing).
Notation byte := ascii.
Notation bytes := string.
Infix ":::" := String
(at level 60, right associativity) : string_scope.

Definition nl : string := "010" ::: "".

Definition string_beq (s1 s2:string) : bool :=
  if string_dec s1 s2 then true else false.

Fixpoint String_rev (s:string) : string :=
  match s with
  | EmptyString => s
  | String a s' => append (String_rev s') (String a EmptyString)
  end. 

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

Fixpoint String_splitAtSub (sub s:string) : option (string * string) :=
  match sub, s with
  | "", _ => Some ("", s)
  | _, "" => None
  | String a sub', String b s' =>
    if ascii_dec a b then String_splitAtSub sub' s'
    else match String_splitAtSub sub s' with
         | None => None
         | Some (s1, s2) => Some (String b s1, s2)
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

Definition hex (b0 b1 b2 b3 : bool) : ascii :=
  match b0, b1, b2, b3 with
  | false, false, false, false => "0"
  | true,  false, false, false => "1"
  | false, true,  false, false => "2"
  | true,  true,  false, false => "3"
  | false, false, true,  false => "4"
  | true,  false, true,  false => "5"
  | false, true,  true,  false => "6"
  | true,  true,  true,  false => "7"
  | false, false, false, true  => "8"
  | true,  false, false, true  => "9"
  | false, true,  false, true  => "A"
  | true,  true,  false, true  => "B"
  | false, false, true,  true  => "C"
  | true,  false, true,  true  => "D"
  | false, true,  true,  true  => "E"
  | true,  true,  true,  true  => "F"
  end.
