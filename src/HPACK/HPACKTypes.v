From Coq Require Import Strings.String BinNat FSets.FMapAVL List Basics.
Import ListNotations.
Require Coq.Structures.OrderedTypeEx.
Open Scope list_scope.
Open Scope string_scope.
Open Scope N_scope.
Open Scope program_scope.

(* https://tools.ietf.org/html/rfc7541#section-1.3 *)
(* Header Field:  A name-value pair.  Both the name and value are
      treated as opaque sequences of octets. *)
Definition HeaderField := (string * string)%type.

(* Dynamic Table:  The dynamic table is a table that
      associates stored header fields with index values.  This table is
      dynamic and specific to an encoding or decoding context.

   Static Table:  The static table is a table that
      statically associates header fields that occur frequently with
      index values.  This table is ordered, read-only, always
      accessible, and it may be shared amongst all encoding or decoding
      contexts. *)
Definition Table := list (N * HeaderField).

(* Dynamic Tables are a pair of a maximum size and a table. The convention is
   that the table has size (as defined in 
   https://tools.ietf.org/html/rfc7541#section-4.1) less than or equal to the
   maximum size.  *)
Definition DTable := (N * Table)%type.

(* Header List:  A header list is an ordered collection of header fields
      that are encoded jointly and can contain duplicate header fields.
      A complete list of header fields contained in an HTTP/2 header
      block is a header list. *)
Definition HeaderList := list string.

(* https://tools.ietf.org/html/rfc7541#section-6 *)
(* Header Field Representation:  A header field can be represented in
      encoded form either as a literal or as an index *)
Inductive HeaderFieldRepresentation :=
(* https://tools.ietf.org/html/rfc7541#section-6.1 *)
| IndexedHF : N -> HeaderFieldRepresentation
(* https://tools.ietf.org/html/rfc7541#section-6.2 *)
| LHFIncrementIndexedName : N -> bool -> string -> HeaderFieldRepresentation
| LHFIncrementNewName : bool -> string -> bool -> string -> HeaderFieldRepresentation
| LHFWithoutIndexIndexedName : N -> bool -> string -> HeaderFieldRepresentation
| LHFWithoutIndexNewName : bool -> string -> bool -> string -> HeaderFieldRepresentation
| LHFNeverIndexIndexedName : N -> bool -> string -> HeaderFieldRepresentation
| LHFNeverIndexNewName : bool -> string -> bool -> string -> HeaderFieldRepresentation
(* https://tools.ietf.org/html/rfc7541#section-6.3 *)
| DTableSizeUpdate : N -> HeaderFieldRepresentation.

(* Header Block:  An ordered list of header field representations,
      which, when decoded, yields a complete header list. *)
Definition HeaderBlock := list HeaderFieldRepresentation.

(* https://tools.ietf.org/html/rfc7541#appendix-A *)
(* https://tools.ietf.org/html/rfc7541#section-2.3.1 *)
Definition static_table : Table :=
  [ (1, (":authority", ""));
    (2, (":method", "GET"));
    (3, (":method", "POST"));
    (4, (":path", "/"));
    (5, (":path", "/index.html"));
    (6, (":scheme", "http"));
    (7, (":scheme", "https"));
    (8, (":status", "200"));
    (9, (":status", "204"));
    (10, (":status", "206"));
    (11, (":status", "304"));
    (12, (":status", "400"));
    (13, (":status", "404"));
    (14, (":status", "500"));
    (15, ("accept-charset", ""));
    (16, ("accept-encoding", "gzip, deflate"));
    (17, ("accept-language", ""));
    (18, ("accept-ranges", ""));
    (19, ("accept", ""));
    (20, ("access-control-allow-origin", ""));
    (21, ("age", ""));
    (22, ("allow", ""));
    (23, ("authorization", ""));
    (24, ("cache-control", ""));
    (25, ("content-disposition", ""));
    (26, ("content-encoding", ""));
    (27, ("content-language", ""));
    (28, ("content-length", ""));
    (29, ("content-location", ""));
    (30, ("content-range", ""));
    (31, ("content-type", ""));
    (32, ("cookie", ""));
    (33, ("date", ""));
    (34, ("etag", ""));
    (35, ("expect", ""));
    (36, ("expires", ""));
    (37, ("from", ""));
    (38, ("host", ""));
    (39, ("if-match", ""));
    (40, ("if-modified-since", ""));
    (41, ("if-none-match", ""));
    (42, ("if-range", ""));
    (43, ("if-unmodified-since", ""));
    (44, ("last-modified", ""));
    (45, ("link", ""));
    (46, ("location", ""));
    (47, ("max-forwards", ""));
    (48, ("proxy-authenticate", ""));
    (49, ("proxy-authorization", ""));
    (50, ("range", ""));
    (51, ("referer", ""));
    (52, ("refresh", ""));
    (53, ("retry-after", ""));
    (54, ("server", ""));
    (55, ("set-cookie", ""));
    (56, ("strict-transport-security", ""));
    (57, ("transfer-encoding", ""));
    (58, ("user-agent", ""));
    (59, ("vary", ""));
    (60, ("via", ""));
    (61, ("www-authenticate", ""))].

(* https://tools.ietf.org/html/rfc7541#section-2.3.3 *)
Definition snd_opt {A} {B} (p:option (A * B)) : option B :=
  match p with
  | Some p => Some (snd p)
  | _ => None
  end.

Definition index_into_tables (i:N) (dynamic_table:DTable) : option HeaderField :=
  let assoc j t := snd_opt (find (fun '(k, _) => N.eqb j k) t) in
  if i =? 0 then None
  else if i <=? N.of_nat (length static_table) then assoc i static_table
       else assoc (i - (N.of_nat (length static_table))) (snd dynamic_table).

(* https://tools.ietf.org/html/rfc7541#section-2.3.2 *)
(* https://tools.ietf.org/html/rfc7541#section-2.3.3 *)
Definition fst_opt {A} {B} (p:option (A * B)) : option A :=
  match p with
  | Some p => Some (fst p)
  | _ => None
  end.

Definition eqb_hf (s1 s2:HeaderField) : bool :=
  match s1, s2 with
  | (fs1, ss1), (fs2, ss2) => andb (if string_dec fs1 fs2 then true else false)
                                  (if string_dec ss1 ss2 then true else false)
  end.

Definition find_dtable (h:HeaderField) (dynamic_table:DTable) : option N :=
  @fst_opt N HeaderField (find (fun '(_, s) => eqb_hf s h) (snd dynamic_table)).

(* The size of an entry is the sum of its name's length in octets (as defined in
   https://tools.ietf.org/html/rfc7541#section-5.2), its value's length in 
   octets, and 32. *)
Definition size_hf (hf:HeaderField) : N :=
  N.of_nat (String.length (fst hf)) + 32.

(* https://tools.ietf.org/html/rfc7541#section-4.1 *)
Definition size_dtable (dynamic_table:DTable) : N :=
  fold_left N.add (map (size_hf ∘ snd) (snd dynamic_table)) 0. 