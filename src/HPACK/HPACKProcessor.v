From HTTP2.HPACK Require Import HPACKTypes HPACKTables.
From HTTP2.Util Require Import Parser.
From Coq Require Import Basics.
From ExtLib Require Import Monads.
Import MonadNotation.

(* https://tools.ietf.org/html/rfc7541#section-3.2 *)
(* Takes a Header Field Representation (which is part of a Header Block) and
   a dynamic table, and processes the hfr, returning either an error,
   or a potentially mutated dynamic table. *)
Definition process_HFR `{Monad Err} `{MonadExc HPACKError Err}
           (hfr:HeaderFieldRepresentation) (dynamic_table:DTable) : Err (option HeaderField * DTable) :=
  match hfr with
  | LHFIncrementIndexedName x s2 =>
    s <- index_into_tables x dynamic_table;;
    ret (Some (fst s, s2), (add_dtable_entry dynamic_table (fst s, s2)))
  | LHFIncrementNewName s1 s2 =>
    ret (Some (s1, s2), (add_dtable_entry dynamic_table (s1, s2)))
  | DTableSizeUpdate x => ret (None, (change_dtable_size x dynamic_table))
  | IndexedHF x => s <- index_into_tables x dynamic_table;; ret (Some s, dynamic_table)
  | LHFWithoutIndexIndexedName x s2 | LHFNeverIndexIndexedName x s2 =>
    s <- index_into_tables x dynamic_table;;
    ret (Some (fst s, s2), dynamic_table)
  | LHFWithoutIndexNewName s1 s2 | LHFNeverIndexNewName s1 s2 =>
                                   ret (Some (s1, s2), dynamic_table)
  end.
