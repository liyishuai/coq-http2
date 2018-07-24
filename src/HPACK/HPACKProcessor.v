From HTTP2.HPACK Require Import HPACKTypes.

(* https://tools.ietf.org/html/rfc7541#section-3.2 *)
(* Takes a Header Field Representation (which is part of a Header Block) and 
   a dynamic table, and processes the hfr, returning a potentially mutated 
   dynamic table.*)
Definition processHFR (hfr:HeaderFieldRepresentation) (dynamic_table:DTable) : DTable :=
  match hfr with
  | LHFIncrementNewName H1 s1 H2 s2 => dynamic_table
  | _ => dynamic_table
  end.
    