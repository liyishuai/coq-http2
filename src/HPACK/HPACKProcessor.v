From HTTP2.HPACK Require Import HPACKTypes HPACKTables.
From HTTP2.Util Require Import Parser.
From Coq Require Import Basics.
From ExtLib Require Import Monads.
Import MonadNotation.

(* https://tools.ietf.org/html/rfc7541#section-3.2 *)
(* Takes a Header Field Representation (which is part of a Header Block) and 
   a dynamic table, and processes the hfr, returning either an error,
   or a potentially mutated dynamic table. *)
Definition processHFR {m:Tycon} `{Monad m} `{MError HPACKError m}
           (hfr:HeaderFieldRepresentation) (dynamic_table:DTable) : m DTable :=
  match hfr with
  | LHFIncrementIndexedName x s2 =>
    s <- index_into_tables x dynamic_table ;;
    ret (add_dtable_entry dynamic_table (fst s, s2))
  | LHFIncrementNewName s1 s2 =>
    ret (add_dtable_entry dynamic_table (s1, s2))
  | DTableSizeUpdate x => ret (change_dtable_size x dynamic_table)
  | IndexedHF _ | LHFWithoutIndexIndexedName _ _
  | LHFWithoutIndexNewName _ _ | LHFNeverIndexIndexedName _ _
  | LHFNeverIndexNewName _ _ => ret dynamic_table
  end.