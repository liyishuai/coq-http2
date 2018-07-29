From Coq Require Import String BinNat Ascii BinNatDef.
From HTTP2.HPACK Require Import HPACKTypes HPACKTables.
From HTTP2.HPACK.Util Require Import HPACKOptionE.
From ExtLib Require Import Monads.
Import MonadNotation.
Open Scope N_scope.
Open Scope string_scope.


(* Decodes a string to an integer where at least the first octet (ascii) is 
   assumed to be an encoded integer. The prefix is a value of n bits.
    https://tools.ietf.org/html/rfc7541#section-5.1

Pseudocode to decode an integer I is as follows:

decode I from the next N bits
if I < 2^N - 1, return I
else
    M = 0
    repeat
        B = next octet
        I = I + (B & 127) * 2^M
        M = M + 7
    while B & 128 == 128
    return I
 *)
Fixpoint decode_integer_h (M:N) (s:string) : OptionE (N * string) :=
  match s with
  | EmptyString => inl decodeError
  | String a s' =>
    let B := N_of_ascii a in
    let I := (BinNatDef.N.land B 127) * 2^M in
    if N.land B 128 =? 128
    then e <- decode_integer_h (M + 7) s' ;;
         ret (I + fst e, snd e)
    else ret (I, s')
  end.

Definition decode_integer (prefix:N) (n:N) (s:string) : OptionE (N * string) :=
  if prefix <? 2^n - 1 then ret (prefix, s)
  else a <- decode_integer_h 0 s ;;
       ret (prefix + fst a, snd a).


(*  https://tools.ietf.org/html/rfc7541#section-5.2 *)
(* Decodes the huffman encoded string s *)
Definition decode_hstring (s:string) : OptionE string := ret "".

(* Splits the string, returning the first n octets in the first of the pair, the 
   rest in the second. *)
Fixpoint get_n_string (s:string) (n:N) : OptionE (string * string) :=
  match s with
  | EmptyString => if n =? 0 then ret ("", "") else inl decodeError
  | String a s' => if n =? 0 then ret ("", s')
                  else e <- get_n_string s' (N.pred n) ;;
                       ret (String a (fst e), snd e)
  end.

(* Decodes an encoded string to a raw string, returning the decoded string as the
   first of the pair, and the rest as the second. *)
Definition decode_string (s:string) : OptionE (string * string) :=
  match s with
  | EmptyString => inl decodeError
  | String a s' =>
    let n := N_of_ascii a in
    let H := N.land n 128 in
    let prefix := N.land n 127 in
    v1 <- decode_integer prefix 7 s' ;;
    v2 <- get_n_string (snd v1) (fst v1) ;;
    if Neqb H 128 then ret v2
    else s'' <- decode_hstring (fst v2) ;; ret (s'', snd v2)
  end.

(* https://tools.ietf.org/html/rfc7541#section-6 *)
(* Decodes a header field representation, returning the rest of the string leftover *)
Definition decode_HFR (s:string) : OptionE (HeaderFieldRepresentation * string) :=
  match s with
  | EmptyString => inl decodeError
  | String a s' =>
    let octet := N_of_ascii a in
    let bit0 := N.land octet 128 in
    (* https://tools.ietf.org/html/rfc7541#section-6.1 *)
    if bit0 =? 128 then fmap (decode_integer (N.land octet 127) 7 s')
                             (fun '(n, s) => ret (IndexedHF n, s))
    else
      let bit1 := N.land octet 64 in
      (* https://tools.ietf.org/html/rfc7541#section-6.2.1 *)
      if bit1 =? 1
      then v <- decode_integer (N.land octet 63) 6 s' ;;
           if fst v =? 0 then v1 <- decode_string (snd v) ;;
                              v2 <- decode_string (snd v1) ;;
                              ret (LHFIncrementNewName (fst v1) (fst v2), snd v2)
           else v1 <- decode_string (snd v) ;;
                ret (LHFIncrementIndexedName (fst v) (fst v1), snd v1)
      else
        (* https://tools.ietf.org/html/rfc7541#section-6.3 *)
        let bit2 := N.land octet 32 in
        if bit2 =? 32 then fmap (decode_integer (N.land octet 31) 5 s')
                                (fun '(n, s) => ret (DTableSizeUpdate n, s))
        else
          (* https://tools.ietf.org/html/rfc7541#section-6.2.3 *)
          let bit3 := N.land octet 16 in
          if bit3 =? 16 then v <- decode_integer (N.land octet 15) 4 s' ;;
                             if fst v =? 0 then v1 <- decode_string (snd v) ;;
                                                v2 <- decode_string (snd v1) ;;
                                                ret (LHFNeverIndexNewName (fst v1)
                                                                          (fst v2),
                                                     snd v2)
                             else v1 <- decode_string (snd v) ;;
                                  ret (LHFNeverIndexIndexedName (fst v)
                                                                (fst v1), snd v1)
          else
            (* https://tools.ietf.org/html/rfc7541#section-6.2.2 *)
            v <- decode_integer (N.land octet 15) 4 s' ;;
            if fst v =? 0 then v1 <- decode_string (snd v) ;;
                               v2 <- decode_string (snd v1) ;;
                               ret (LHFWithoutIndexNewName (fst v1) (fst v2), snd v2)
              else v1 <- decode_string (snd v) ;;
                   ret (LHFWithoutIndexIndexedName (fst v) (fst v1), snd v1)
  end.