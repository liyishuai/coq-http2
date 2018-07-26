From HTTP2.HPACK Require Import HPACKTypes.
From Coq Require Import BinNat List Logic String Ascii Basics.
Import ListNotations.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.
Open Scope list_scope.
Open Scope N_scope.
Open Scope program_scope.

(* https://tools.ietf.org/html/rfc7541#section-5.1
   
   encodes an unsigned integer i with a prefix of n bits.
   Returns a list of bools. This could be changed in the future,
   but for now since the result varies in length depending on
   the value of i, this might be the best approach. 

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
    assert ((i <? 128) <> true).
    intros contra; rewrite contra in H; contradiction.
    rewrite H0 in H2; rewrite N.nlt_ge in H2; apply N.div_lt;
      try (compute; reflexivity); eapply (N.lt_le_trans _ 128);
        eauto; compute; reflexivity.
Defined.
Obligation 3.
  apply N.lt_wf_0.
Defined.

(* Encodes as list of bools (binary number in msb) *)
Fixpoint encode_N (i:N) (n:nat) : list bool :=
  if i <? 2^(N.of_nat n)-1
  then encode_N_help i n
  else encode_N_help (2^(N.of_nat n) - 1) n
       ++ encode_N_help_rec (i - (2^(N.of_nat n) - 1)).

(* https://tools.ietf.org/html/rfc7541#section-5.2 *)
(* Convert string to list of bools (binary number in msb) *)
Fixpoint string_to_bool_list (s:string) : list bool :=
  match s with
  | EmptyString => []
  | String (Ascii b7 b6 b5 b4 b3 b2 b1 b0) s' =>
    b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: string_to_bool_list s'
  end.

(** TODO: Huffman Encoding **)
Definition huffman_string (s:string) : list bool := [].

(* Encodes as list of bools (binary number in msb) *)
Definition encode_string (H:bool) (s:string) : list bool :=
  H :: encode_N (N.of_nat (length s)) 7 ++
    if H then huffman_string s
      else string_to_bool_list s. 

(* https://tools.ietf.org/html/rfc7541#section-6.1 *)
Definition encode_IndexedHF (i:N) : list bool :=
  true :: encode_N i 7.

(* https://tools.ietf.org/html/rfc7541#section-6.2.1 *)
Definition encode_LHFIncrementIndexedName (i1:N) (H2:bool) (s2:string) : list bool :=
  false :: true :: encode_N i1 6
        ++ encode_string H2 s2.

(* https://tools.ietf.org/html/rfc7541#section-6.2.1 *)
Definition encode_LHFIncrementNewName (H1:bool) (s1:string) (H2:bool) (s2:string) : list bool :=
  encode_N 64 8 ++ encode_string H1 s1 ++ encode_string H2 s2.


(* https://tools.ietf.org/html/rfc7541#section-6.2.2 *)
Definition encode_LHFWithoutIndexIndexedName (i1:N) (H2:bool) (s2:string) : list bool :=
  false :: false :: false :: false :: encode_N i1 4
        ++ encode_string H2 s2.

(* https://tools.ietf.org/html/rfc7541#section-6.2.2 *)
Definition encode_LHFWithoutIndexNewName (H1:bool) (s1:string) (H2:bool) (s2:string) : list bool :=
  encode_N 0 8 ++ encode_string H1 s1 ++ encode_string H2 s2.

(* https://tools.ietf.org/html/rfc7541#section-6.2.3 *)
Definition encode_LHFNeverIndexIndexedName (i1:N) (H2:bool) (s2:string) : list bool :=
  false :: false :: false :: true :: encode_N i1 4
        ++ encode_string H2 s2.

(* https://tools.ietf.org/html/rfc7541#section-6.2.3 *)
Definition encode_LHFNeverIndexNewName (H1:bool) (s1:string) (H2:bool) (s2:string) : list bool :=
  encode_N 16 8 ++ encode_string H1 s1 ++ encode_string H2 s2.

(* https://tools.ietf.org/html/rfc7541#section-6.3 *)
Definition encode_DTableSizeUpdate (i:N) : list bool :=
  false :: false :: true :: encode_N i 5.

(* https://tools.ietf.org/html/rfc7541#section-6 *)
Definition encode_hfr (hfr:HeaderFieldRepresentation) : list bool :=
  match hfr with
  | IndexedHF i => encode_IndexedHF i
  | LHFIncrementIndexedName i h2 s2 => encode_LHFIncrementIndexedName i h2 s2
  | LHFIncrementNewName h1 s1 h2 s2 => encode_LHFIncrementNewName h1 s1 h2 s2
  | LHFWithoutIndexIndexedName i h2 s2 => encode_LHFWithoutIndexIndexedName i h2 s2
  | LHFWithoutIndexNewName h1 s1 h2 s2 => encode_LHFWithoutIndexNewName h1 s1 h2 s2
  | LHFNeverIndexIndexedName i h2 s2 => encode_LHFNeverIndexIndexedName i h2 s2
  | LHFNeverIndexNewName h1 s1 h2 s2 => encode_LHFNeverIndexNewName h1 s1 h2 s2
  | DTableSizeUpdate i => encode_DTableSizeUpdate i
  end.

Fixpoint pack_list_bool (b:list bool) : string :=
  match b with
  | b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: tl =>
    String (Ascii b0 b1 b2 b3 b4 b5 b6 b7) (pack_list_bool tl)
  | _ => ""
  end.

Definition encode_headerBlock (hb: HeaderBlock) : HeaderList :=
  map (pack_list_bool ∘ encode_hfr) hb.