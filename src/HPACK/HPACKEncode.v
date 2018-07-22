From HTTP2.HPACK Require Import HPACKTypes.
From Coq Require Import BinNat List Logic.
Import ListNotations.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.
Open Scope list_scope.
Open Scope N_scope.

(* encodes an unsigned integer i with a prefix of n bits.
   Returns a list of bools. This could be changed in the future,
   but for now since the result varies in length depending on
   the value of i, this might be the best approach. 
   https://tools.ietf.org/html/rfc7541#section-5.1

   Pseudocode to represent an integer I is as follows:

   if I < 2^N - 1, encode I on N bits
   else
       encode (2^N - 1) on N bits
       I = I - (2^N - 1)
       while I >= 128
            encode (I % 128 + 128) on 8 bits
            I = I / 128
       encode I on 8 bits *)
Fixpoint encode_N_help (i:N) (n:nat) : list bool :=
  match n with
  | O => []
  | S n' =>
    (if (N.shiftr_nat i n') mod 2 =? 0 then false else true) :: encode_N_help i n'
  end.

Program Fixpoint encode_N_help_rec (i:N) {measure i ( N.lt )} : list bool :=
  match i <? 128 with
  | true => encode_N_help i 8
  | _ =>
    encode_N_help ((i mod 128) + 128) 8
                  ++ encode_N_help_rec (i / 128)
  end.
Obligation 1.
  pose proof (N.ltb_lt i 128); pose proof not_iff_compat; apply H1 in H0;
    assert ((i <? 128) <> true);
    try solve [intros contra; rewrite contra in H; contradiction];
    rewrite H0 in H2; rewrite N.nlt_ge in H2; apply N.div_lt;
      try (compute; reflexivity); eapply (N.lt_le_trans _ 128);
        eauto; compute; reflexivity.
Defined.
Obligation 3.
  apply N.lt_wf_0.
Defined.

Fixpoint encode_N (i:N) (n:nat) : list bool :=
  if i <? 2^(N.of_nat n)-1
  then encode_N_help i n
  else encode_N_help (2^(N.of_nat n) - 1) n
       ++ encode_N_help_rec (i - (2^(N.of_nat n) - 1)).