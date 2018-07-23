From Coq Require Import String BinNat FSets.FMapAVL List.
Import ListNotations.
Require Coq.Structures.OrderedTypeEx.
Open Scope list_scope.
Open Scope string_scope.
Open Scope N_scope.

(* https://tools.ietf.org/html/rfc7541#section-6 *)
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

Module NM := FMapAVL.Make (Coq.Structures.OrderedTypeEx.N_as_OT).
Definition NMap := NM.t.
Definition Table := NMap (string * string).

Definition add {a} k (v:a) := NM.add k v.
Definition delete {a} k (m:NMap a) := NM.remove k m.
Definition member {a} k (m:NMap a) := NM.mem k m.
Definition lookup {a} k (m:NMap a) := NM.find k m.
Definition empty {a} := @NM.empty a.

(* https://tools.ietf.org/html/rfc7541#appendix-A *)
(* https://tools.ietf.org/html/rfc7541#section-2.3.1 *)
Definition static_table : Table :=
  fold_left (fun m '(i, v) => add i v m)
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
              (61, ("www-authenticate", ""))] empty.