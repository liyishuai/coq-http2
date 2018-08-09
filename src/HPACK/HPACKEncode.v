From HTTP2.HPACK Require Import HPACKTypes HPACKTables.
From Coq Require Import BinNat List Logic String Ascii Basics Recdef.
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

Function encode_N_help_rec (i:N) {wf (N.lt) i } : list bool :=
  match i <? 128 with
  | true => encode_N_help i 8
  | _ =>
    encode_N_help ((i mod 128) + 128) 8
                  ++ encode_N_help_rec (i / 128)
  end.
Proof. 
  intros. 
  pose proof (N.ltb_lt i 128); pose proof not_iff_compat; apply H0 in H;
    assert ((i <? 128) <> true).
    intros contra; rewrite contra in teq; inversion teq.
    rewrite H in H1. rewrite N.nlt_ge in H1; apply N.div_lt;
      try (compute; reflexivity); eapply (N.lt_le_trans _ 128);
        eauto; compute; reflexivity.
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

Fixpoint huffman_string (s:string) : list bool :=
  match s with
  | EmptyString => []
  | String a s' =>
    match find (fun x => BinNatDef.N.eqb (N_of_ascii a) (fst x)) huffman_table with
    | None => [] (* Unreachable *)
    | Some l => snd l
    end ++ huffman_string s'
  end.

(* Encodes as list of bools (binary number in msb) *)
Definition encode_string (H:bool) (s:string) : list bool :=
  H :: 
    if H then
      let y := huffman_string s in
      let x := N.of_nat (List.length y) in
      let len := x / 8 in
      encode_N (len + 1) 7 ++ y ++
               if x mod 8 =? 0 then repeat true (N.to_nat 8)
               else repeat true (N.to_nat (8 - (x mod 8)))
    else encode_N (N.of_nat (length s)) 7 ++ string_to_bool_list s. 

(* https://tools.ietf.org/html/rfc7541#section-6.1 *)
Definition encode_IndexedHF (i:N) : list bool :=
  true :: encode_N i 7.

(* https://tools.ietf.org/html/rfc7541#section-6.2.1 *)
Definition encode_LHFIncrementIndexedName (i1:N) (H:bool) (s2:string) : list bool :=
  false :: true :: encode_N i1 6
        ++ encode_string H s2.

(* https://tools.ietf.org/html/rfc7541#section-6.2.1 *)
Definition encode_LHFIncrementNewName (H:bool) (s1:string)
           (s2:string) : list bool :=
  encode_N 64 8 ++ encode_string H s1 ++ encode_string H s2.


(* https://tools.ietf.org/html/rfc7541#section-6.2.2 *)
Definition encode_LHFWithoutIndexIndexedName (i1:N) (H:bool) (s2:string) : list bool :=
  false :: false :: false :: false :: encode_N i1 4
        ++ encode_string H s2.

(* https://tools.ietf.org/html/rfc7541#section-6.2.2 *)
Definition encode_LHFWithoutIndexNewName (H:bool) (s1:string)
           (s2:string) : list bool :=
  encode_N 0 8 ++ encode_string H s1 ++ encode_string H s2.

(* https://tools.ietf.org/html/rfc7541#section-6.2.3 *)
Definition encode_LHFNeverIndexIndexedName (i1:N) (H:bool) (s2:string) : list bool :=
  false :: false :: false :: true :: encode_N i1 4
        ++ encode_string H s2.

(* https://tools.ietf.org/html/rfc7541#section-6.2.3 *)
Definition encode_LHFNeverIndexNewName (H:bool) (s1:string)
           (s2:string) : list bool :=
  encode_N 16 8 ++ encode_string H s1 ++ encode_string H s2.

(* https://tools.ietf.org/html/rfc7541#section-6.3 *)
Definition encode_DTableSizeUpdate (i:N) : list bool :=
  false :: false :: true :: encode_N i 5.

(* https://tools.ietf.org/html/rfc7541#section-6 *)
(* H corresponds to whether huffman encoding is being used *)
Definition encode_HFR (H:bool) (hfr:HeaderFieldRepresentation) : list bool :=
  match hfr with
  | IndexedHF i => encode_IndexedHF i
  | LHFIncrementIndexedName i s2 => encode_LHFIncrementIndexedName i H s2
  | LHFIncrementNewName s1 s2 => encode_LHFIncrementNewName H s1 s2
  | LHFWithoutIndexIndexedName i s2 => encode_LHFWithoutIndexIndexedName i H s2
  | LHFWithoutIndexNewName s1 s2 => encode_LHFWithoutIndexNewName H s1 s2
  | LHFNeverIndexIndexedName i s2 => encode_LHFNeverIndexIndexedName i H s2
  | LHFNeverIndexNewName s1 s2 => encode_LHFNeverIndexNewName H s1 s2
  | DTableSizeUpdate i => encode_DTableSizeUpdate i
  end.

Fixpoint pack_list_bool (b:list bool) : string :=
  match b with
  | b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: tl =>
    String (Ascii b0 b1 b2 b3 b4 b5 b6 b7) (pack_list_bool tl)
  | _ => ""
  end.

(* H corresponds to whether huffman encoding is being used *)
Definition encode_HB  (H:bool) (hb: HeaderBlock) : HeaderList :=
  map (pack_list_bool ∘ (encode_HFR H)) hb.