From HTTP2.HPACK Require Import HPACKTypes HPACKTables HPACKDecode
     Util.HPACKOptionE.
From Coq Require Import Basics.
From ExtLib Require Import Monads.
Import MonadNotation.

(* https://tools.ietf.org/html/rfc7541#section-3.2 *)
(* Takes a Header Field Representation (which is part of a Header Block) and 
   a dynamic table, and processes the hfr, returning either an error,
   or a potentially mutated dynamic table. *)
Definition processHFR (hfr:HeaderFieldRepresentation) (dynamic_table:DTable)
  : OptionE DTable :=
  let dec_str (H:bool) s := if H then decode_hstring s else s in
  match hfr with
  | LHFIncrementIndexedName x H2 s2 =>
    s <- index_into_tables x dynamic_table ;;
    ret (add_dtable_entry dynamic_table (fst s, dec_str H2 s2))
  | LHFIncrementNewName H1 s1 H2 s2 =>
    ret (add_dtable_entry dynamic_table (dec_str H1 s1, dec_str H2 s2))
  | DTableSizeUpdate x => ret (change_dtable_size x dynamic_table)
  | IndexedHF _ | LHFWithoutIndexIndexedName _ _ _
  | LHFWithoutIndexNewName _ _ _ _ | LHFNeverIndexIndexedName _ _ _
  | LHFNeverIndexNewName _ _ _ _ => ret dynamic_table
  end.