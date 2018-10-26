From Coq Require Import String BinNat Ascii BinNatDef Vector List.
From HTTP2 Require Import
     Equiv
     Types.
From HTTP2.Util Require Import
     BitVector
     Parser
     VectorUtil
     StringUtil.
From HTTP2.HPACK Require Import HPACKTypes HPACKTables.
From ExtLib Require Import Monads.
Import MonadNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope N_scope.
Open Scope monad_scope.
Open Scope list_scope.

(* Decodes a string to an integer where at least the first octet (ascii) is
   assumed to be an encoded integer. The prefix is a value of n bits.
    https://tools.ietf.org/html/rfc7541#section-5.1

Pseudocode to decode an integer I with an N bit prefix is as follows:

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
Fixpoint decode_integer_h {m:Tycon} `{Monad m} `{MonadExc HPACKError m}
           `{MParser byte m} (fuel:nat) (M:N) : m N :=
  match fuel with
  | O =>  raise IntegerOverflow
  | S fuel' => a <- get_byte ;;
            let B := (N_of_ascii a) in
            let I := (BinNatDef.N.land B 127) * 2^M in
            if N.land B 128 =? 128
            then e <- decode_integer_h (fuel') (M + 7);;
                 ret (I + e)
            else ret I
  end.

(* To justify using fuel (and the value) in decode_integer_h:

   "Integer encodings that exceed implementation limits -- in
    value or octet length -- MUST be treated as decoding errors.
    Different limits can be set for each of the different uses of
    integers, based on implementation constraints."

   For fuel, I used 100, because integers are only used as indices,
   which means the dynamic table would have to have size 2^100 for this
   to be a problem.

   Alternatively, the fuel could be a parameter passed in from when the
   header block fragments are combined to form a header block, or used in
   an MParser with an internal fuel.
*)
Definition decode_integer {m:Tycon} `{Monad m} `{MonadExc HPACKError m}
           `{MParser byte m} (prefix:N) (n:N) : m N :=
  if prefix <? 2^n - 1 then ret prefix
  else a <- decode_integer_h 0 100 ;;
       ret (prefix + a).

(*  https://tools.ietf.org/html/rfc7541#section-5.2 *)
(* Decodes the huffman encoded string s *)
Definition list_eqb (l1 l2: list bool) :=
  if list_eq_dec Bool.bool_dec l1 l2 then true else false.

Program Fixpoint lookup (l:list bool) { measure (length l) } :=
  match l with
  | [] => None
  | _ =>
    match find (fun '(a, bs) => list_eqb l bs) huffman_table with
    | None =>
      let a := last l false in
      let l' := removelast l in
      option_map (fun '(v, l) => (v, l ++ [a])) (lookup l')
    | Some v =>
      Some (fst v, [])
    end
  end.
Obligation 1. apply removelast_decreasing; auto.
Defined.

(* Double check this code, maybe rewrite for clarity *)
Fixpoint decode_hstring_h {m:Tycon} `{Monad m} `{MonadExc HPACKError m}
         `{MParser byte m} (buffer:list bool) (s:string) : m string :=
  match s with
  | EmptyString =>
    if PeanoNat.Nat.ltb (length buffer) 8 && fold_left (fun acc b => b && acc) buffer true
    then ret "" else raise EmptyEncodedString
  | String a s' =>
    match a with
    | Ascii b7 b6 b5 b4 b3 b2 b1 b0 =>
      (* To catch the case where an entire huffman encoded string is contained
         in b0-b7, run lookup twice.
         Note since a requirement of huffman is that no encoded string is a prefix
         of another encoded string, it's safe to look further, ie look at all 8 bits
         first. *)
      let buffer' := (buffer ++ [b0; b1; b2; b3; b4; b5; b6; b7]) in
      match lookup buffer' with
      | None => decode_hstring_h buffer' s'
      | Some (a, l) =>
        if a =? 256 then raise EosInTheMiddle
        else
          match lookup l with
          | None =>
            v <- decode_hstring_h l s';;
            ret (String (ascii_of_N a) v)
          | Some (b, l') =>
            v <- decode_hstring_h l' s';;
            ret (String (ascii_of_N a) (String (ascii_of_N b) v))
          end
      end
    end
  end.

Definition decode_hstring {m:Tycon} `{Monad m} `{MonadExc HPACKError m}
           `{MParser byte m} (s:string) : m string :=
  decode_hstring_h List.nil s.

(* Decodes an encoded string to a raw string. *)
Definition decode_string {m:Tycon} `{Monad m} `{MonadExc HPACKError m}
           `{MParser byte m} : m string :=
  a <- get_byte ;;
  let n := N_of_ascii a in
  let prefix := N.land n 127 in
  len <- decode_integer prefix 7 ;;
  s <- get_bytes_N len ;;
  let H := N.land n 128 in
  if BinNat.N.eqb H 128 then decode_hstring s
  else ret s.

(* https://tools.ietf.org/html/rfc7541#section-6 *)
(* Decodes a header field representation *)
Definition decode_HFR {m:Tycon} `{Monad m} `{MonadExc HPACKError m}
           `{MParser byte m} : m HeaderFieldRepresentation :=
  a <- get_byte ;;
  let octet := N_of_ascii a in
  let bit0 := N.land octet 128 in
  (* https://tools.ietf.org/html/rfc7541#section-6.1 *)
  if bit0 =? 128 then n <- decode_integer (N.land octet 127) 7;;
                      ret (IndexedHF n)
  else
    let bit1 := N.land octet 64 in
    (* https://tools.ietf.org/html/rfc7541#section-6.2.1 *)
    if bit1 =? 64
    then v <- decode_integer (N.land octet 63) 6;;
         if v =? 0 then v1 <- decode_string;;
                        v2 <- decode_string;;
                        ret (LHFIncrementNewName v1 v2)
           else v1 <- decode_string;;
                ret (LHFIncrementIndexedName v v1)
    else
      (* https://tools.ietf.org/html/rfc7541#section-6.3 *)
      let bit2 := N.land octet 32 in
      if bit2 =? 32 then n <- decode_integer (N.land octet 31) 5;;
                         ret (DTableSizeUpdate n)
      else
        (* https://tools.ietf.org/html/rfc7541#section-6.2.3 *)
        let bit3 := N.land octet 16 in
        if bit3 =? 16 then v <- decode_integer (N.land octet 15) 4;;
                           if v =? 0 then v1 <- decode_string;;
                                          v2 <- decode_string;;
                                          ret (LHFNeverIndexNewName v1 v2)
                           else v1 <- decode_string;;
                                ret (LHFNeverIndexIndexedName v v1)
        else
          (* https://tools.ietf.org/html/rfc7541#section-6.2.2 *)
          v <- decode_integer (N.land octet 15) 4;;
          if v =? 0 then v1 <- decode_string;;
                         v2 <- decode_string;;
                         ret (LHFWithoutIndexNewName v1 v2)
          else v1 <- decode_string;;
               ret (LHFWithoutIndexIndexedName v v1).

Fixpoint decode_HB_h {m:Tycon} `{Monad m} `{MonadExc HPACKError m}
         `{MParser byte m} (n:nat) : m HeaderBlock :=
  match n with
  | O => raise HeaderBlockOverflow
  | S n' =>
    h <- decode_HFR;;
    hs <- catch (decode_HB_h n') (fun e =>
                            match e with
                            | HeaderBlockTruncated =>
                              ret []
                            | _ => raise e
                            end);;
    ret (h :: hs)
  end.

Definition decode_HB {m:Tycon} `{Monad m} `{MonadExc HPACKError m}
           `{MParser byte m} : m HeaderBlock :=
  decode_HB_h 1000.
