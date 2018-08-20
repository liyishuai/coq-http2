From HTTP2.src.HPACK Require Import HPACKTypes.
From HTTP2.src Require Import Types Util.Parser.
From Coq Require Import Strings.String BinNat Lists.List Basics.
From ExtLib Require Import Monad MonadExc.
Import ListNotations MonadNotation.
Require Coq.Structures.OrderedTypeEx Program.Wf.
Open Scope list_scope.
Open Scope string_scope.
Open Scope N_scope.
Open Scope program_scope.
Open Scope monad_scope.

(* https://tools.ietf.org/html/rfc7541#appendix-A *)
(* https://tools.ietf.org/html/rfc7541#section-2.3.1 *)
Definition static_table : Table :=
  [ (":authority", "");
    (":method", "GET");
    (":method", "POST");
    (":path", "/");
    (":path", "/index.html");
    (":scheme", "http");
    (":scheme", "https");
    (":status", "200");
    (":status", "204");
    (":status", "206");
    (":status", "304");
    (":status", "400");
    (":status", "404");
    (":status", "500");
    ("accept-charset", "");
    ("accept-encoding", "gzip, deflate");
    ("accept-language", "");
    ("accept-ranges", "");
    ("accept", "");
    ("access-control-allow-origin", "");
    ("age", "");
    ("allow", "");
    ("authorization", "");
    ("cache-control", "");
    ("content-disposition", "");
    ("content-encoding", "");
    ("content-language", "");
    ("content-length", "");
    ("content-location", "");
    ("content-range", "");
    ("content-type", "");
    ("cookie", "");
    ("date", "");
    ("etag", "");
    ("expect", "");
    ("expires", "");
    ("from", "");
    ("host", "");
    ("if-match", "");
    ("if-modified-since", "");
    ("if-none-match", "");
    ("if-range", "");
    ("if-unmodified-since", "");
    ("last-modified", "");
    ("link", "");
    ("location", "");
    ("max-forwards", "");
    ("proxy-authenticate", "");
    ("proxy-authorization", "");
    ("range", "");
    ("referer", "");
    ("refresh", "");
    ("retry-after", "");
    ("server", "");
    ("set-cookie", "");
    ("strict-transport-security", "");
    ("transfer-encoding", "");
    ("user-agent", "");
    ("vary", "");
    ("via", "");
    ("www-authenticate", "")].

(* https://tools.ietf.org/html/rfc7541#section-2.3.3 *)
Definition index_into_tables {m:Tycon} `{Monad m} `{MonadExc HPACKError m} (i:N)
           (dynamic_table:DTable) : m HeaderField :=
  if i =? 0 then raise (IndexOverrun i)
  else if i <=? N.of_nat (length static_table)
       then opt_err (IndexOverrun i)
                    (nth_error static_table (N.to_nat i))
       else opt_err (IndexOverrun i)
                    (nth_error (snd dynamic_table)
                               (N.to_nat i - (length static_table + 1))%nat).

(* https://tools.ietf.org/html/rfc7541#section-2.3.2 *)
(* https://tools.ietf.org/html/rfc7541#section-2.3.3 *)
Definition eqb_hf (s1 s2:HeaderField) : bool :=
  match s1, s2 with
  | (fs1, ss1), (fs2, ss2) => andb (if string_dec fs1 fs2 then true else false)
                                  (if string_dec ss1 ss2 then true else false)
  end.

Definition find_table_h (h:HeaderField) (t:Table) : option N :=
  let fix loop i l :=
      match l with
      | [] => None 
      | a :: tl =>
        if eqb_hf h a then Some i else loop (N.succ i) (tl)
      end in
  loop 1 t.

Definition find_table (h:HeaderField) (dynamic_table:DTable) : option N :=
  match (find_table_h h static_table) with
  | None =>
    match (find_table_h h (snd dynamic_table)) with
    | None => None
    | Some x => Some (x + N.of_nat (length static_table))
    end
  | Some x => Some x
  end.

(* The size of an entry is the sum of its name's length in octets (as defined in
   https://tools.ietf.org/html/rfc7541#section-5.2), its value's length in 
   octets, and 32. *)
Definition size_hf (hf:HeaderField) : N :=
  N.of_nat (String.length (fst hf)) + 32.

(* https://tools.ietf.org/html/rfc7541#section-4.1 *)
Definition size_dtable (dynamic_table:DTable) : N :=
  fold_left N.add (map size_hf (snd dynamic_table)) 0.


(* https://tools.ietf.org/html/rfc7541#section-4.3 *)
(* https://tools.ietf.org/html/rfc7541#section-4.4 *)
Lemma removelast_decreasing : forall A (l:list A),
    l <> [] -> (length (removelast l) < length l)%nat.
Proof.
  intros. specialize exists_last with (l:=l); intros exists_last.
  apply exists_last in H. inversion H. inversion X. rewrite H0.
    rewrite removelast_app; try congruence. simpl. repeat rewrite app_length.
    simpl. rewrite PeanoNat.Nat.add_0_r. rewrite PeanoNat.Nat.add_1_r.
    apply PeanoNat.Nat.lt_succ_diag_r.
Qed.

Program Fixpoint dtable_entry_eviction (dynamic_table:DTable)
        {measure (length (snd dynamic_table))}: DTable :=
  match size_dtable dynamic_table <=? fst dynamic_table with
  | true => dynamic_table
  | false => dtable_entry_eviction (fst dynamic_table,
                                   removelast (snd dynamic_table))
  end.
Obligation 1.
  symmetry in Heq_anonymous; rewrite N.leb_gt in Heq_anonymous.
  destruct dynamic_table; destruct t.
  - simpl in *. compute in Heq_anonymous; destruct n; inversion Heq_anonymous.
  - cut (snd (n, h :: t) <> []); intros; try solve [simpl; congruence].
    apply removelast_decreasing; auto.
Defined.

Definition change_dtable_size (i:N) (dynamic_table:DTable) : DTable :=
  dtable_entry_eviction (i, snd dynamic_table).

Definition cons_dtable (entry:HeaderField) (dynamic_table:DTable) : DTable :=
  (fst dynamic_table, entry :: snd dynamic_table).

Definition add_dtable_entry (dynamic_table:DTable) (entry:HeaderField)
  : DTable :=
  (* First, evict entries so that the table can add the entry (removes elements
     if table is non empty and adding element pushes table over max size), add
     entry to table, and finally evict entries if table is now too large 
     (removes just entry added only when entry is larger than max table size) *)
  let evict1 := change_dtable_size (fst dynamic_table - size_hf entry)
                                   dynamic_table in
  (change_dtable_size (fst dynamic_table)) (cons_dtable entry evict1).

(* Maps an ascii (+ 256) to a huffman encoded binary number *)
Definition huffman_table : list (N * list bool) :=
  [ ( 0, [true;true;true;true;true;true;true;true;true;true;false;false;false]);
      ( 1, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;false;false]);
      ( 2, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true;false]);
      ( 3, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true;true]);
      ( 4, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false;false]);
      ( 5, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false;true]);
      ( 6, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;false]);
      ( 7, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;true]);
      ( 8, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;false]);
      ( 9, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;false]);
      (10, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false]);
      (11, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;true]);
      (12, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;false]);
      (13, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true]);
      (14, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;true]);
      (15, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;false]);
      (16, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;true]);
      (17, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;false]);
      (18, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;true]);
      (19, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false]);
      (20, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true]);
      (21, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false]);
      (22, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false]);
      (23, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true]);
      (24, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false]);
      (25, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true]);
      (26, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false]);
      (27, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true]);
      (28, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false]);
      (29, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true]);
      (30, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false]);
      (31, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true]);
      (32, [false;true;false;true;false;false]);
      (33, [true;true;true;true;true;true;true;false;false;false]);
      (34, [true;true;true;true;true;true;true;false;false;true]);
      (35, [true;true;true;true;true;true;true;true;true;false;true;false]);
      (36, [true;true;true;true;true;true;true;true;true;true;false;false;true]);
      (37, [false;true;false;true;false;true]);
      (38, [true;true;true;true;true;false;false;false]);
      (39, [true;true;true;true;true;true;true;true;false;true;false]);
      (40, [true;true;true;true;true;true;true;false;true;false]);
      (41, [true;true;true;true;true;true;true;false;true;true]);
      (42, [true;true;true;true;true;false;false;true]);
      (43, [true;true;true;true;true;true;true;true;false;true;true]);
      (44, [true;true;true;true;true;false;true;false]);
      (45, [false;true;false;true;true;false]);
      (46, [false;true;false;true;true;true]);
      (47, [false;true;true;false;false;false]);
      (48, [false;false;false;false;false]);
      (49, [false;false;false;false;true]);
      (50, [false;false;false;true;false]);
      (51, [false;true;true;false;false;true]);
      (52, [false;true;true;false;true;false]);
      (53, [false;true;true;false;true;true]);
      (54, [false;true;true;true;false;false]);
      (55, [false;true;true;true;false;true]);
      (56, [false;true;true;true;true;false]);
      (57, [false;true;true;true;true;true]);
      (58, [true;false;true;true;true;false;false]);
      (59, [true;true;true;true;true;false;true;true]);
      (60, [true;true;true;true;true;true;true;true;true;true;true;true;true;false;false]);
      (61, [true;false;false;false;false;false]);
      (62, [true;true;true;true;true;true;true;true;true;false;true;true]);
      (63, [true;true;true;true;true;true;true;true;false;false]);
      (64, [true;true;true;true;true;true;true;true;true;true;false;true;false]);
      (65, [true;false;false;false;false;true]);
      (66, [true;false;true;true;true;false;true]);
      (67, [true;false;true;true;true;true;false]);
      (68, [true;false;true;true;true;true;true]);
      (69, [true;true;false;false;false;false;false]);
      (70, [true;true;false;false;false;false;true]);
      (71, [true;true;false;false;false;true;false]);
      (72, [true;true;false;false;false;true;true]);
      (73, [true;true;false;false;true;false;false]);
      (74, [true;true;false;false;true;false;true]);
      (75, [true;true;false;false;true;true;false]);
      (76, [true;true;false;false;true;true;true]);
      (77, [true;true;false;true;false;false;false]);
      (78, [true;true;false;true;false;false;true]);
      (79, [true;true;false;true;false;true;false]);
      (80, [true;true;false;true;false;true;true]);
      (81, [true;true;false;true;true;false;false]);
      (82, [true;true;false;true;true;false;true]);
      (83, [true;true;false;true;true;true;false]);
      (84, [true;true;false;true;true;true;true]);
      (85, [true;true;true;false;false;false;false]);
      (86, [true;true;true;false;false;false;true]);
      (87, [true;true;true;false;false;true;false]);
      (88, [true;true;true;true;true;true;false;false]);
      (89, [true;true;true;false;false;true;true]);
      (90, [true;true;true;true;true;true;false;true]);
      (91, [true;true;true;true;true;true;true;true;true;true;false;true;true]);
      (92, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false]);
      (93, [true;true;true;true;true;true;true;true;true;true;true;false;false]);
      (94, [true;true;true;true;true;true;true;true;true;true;true;true;false;false]);
      (95, [true;false;false;false;true;false]);
      (96, [true;true;true;true;true;true;true;true;true;true;true;true;true;false;true]);
      (97, [false;false;false;true;true]);
      (98, [true;false;false;false;true;true]);
      (99, [false;false;true;false;false]);
      (100, [true;false;false;true;false;false]);
      (101, [false;false;true;false;true]);
      (102, [true;false;false;true;false;true]);
      (103, [true;false;false;true;true;false]);
      (104, [true;false;false;true;true;true]);
      (105, [false;false;true;true;false]);
      (106, [true;true;true;false;true;false;false]);
      (107, [true;true;true;false;true;false;true]);
      (108, [true;false;true;false;false;false]);
      (109, [true;false;true;false;false;true]);
      (110, [true;false;true;false;true;false]);
      (111, [false;false;true;true;true]);
      (112, [true;false;true;false;true;true]);
      (113, [true;true;true;false;true;true;false]);
      (114, [true;false;true;true;false;false]);
      (115, [false;true;false;false;false]);
      (116, [false;true;false;false;true]);
      (117, [true;false;true;true;false;true]);
      (118, [true;true;true;false;true;true;true]);
      (119, [true;true;true;true;false;false;false]);
      (120, [true;true;true;true;false;false;true]);
      (121, [true;true;true;true;false;true;false]);
      (122, [true;true;true;true;false;true;true]);
      (123, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;false]);
      (124, [true;true;true;true;true;true;true;true;true;false;false]);
      (125, [true;true;true;true;true;true;true;true;true;true;true;true;false;true]);
      (126, [true;true;true;true;true;true;true;true;true;true;true;false;true]);
      (127, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false]);
      (128, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;false]);
      (129, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;true;false]);
      (130, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;true]);
      (131, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;false]);
      (132, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;true;true]);
      (133, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;false;false]);
      (134, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;false;true]);
      (135, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;false;true]);
      (136, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;true;false]);
      (137, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;true;false]);
      (138, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;true;true]);
      (139, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;false;false]);
      (140, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;false;true]);
      (141, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;true;false]);
      (142, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;true]);
      (143, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;true;true]);
      (144, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;false]);
      (145, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;true]);
      (146, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;true;true]);
      (147, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false;false]);
      (148, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;false]);
      (149, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false;true]);
      (150, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true;false]);
      (151, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true;true]);
      (152, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false;false]);
      (153, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;false;false]);
      (154, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;false;false]);
      (155, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false;true]);
      (156, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;false;true]);
      (157, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;false]);
      (158, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;true]);
      (159, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;true]);
      (160, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;true;false]);
      (161, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;false;true]);
      (162, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;true]);
      (163, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;true;true]);
      (164, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;false;false]);
      (165, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;false]);
      (166, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;true]);
      (167, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;true;false]);
      (168, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;false]);
      (169, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;false;true]);
      (170, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;true;false]);
      (171, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false]);
      (172, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;true;true]);
      (173, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;true;true]);
      (174, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;true]);
      (175, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;false]);
      (176, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false;false]);
      (177, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false;true]);
      (178, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false;false]);
      (179, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true;false]);
      (180, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;true]);
      (181, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false;true]);
      (182, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;false]);
      (183, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;true]);
      (184, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;false]);
      (185, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true;false]);
      (186, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true;true]);
      (187, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false;false]);
      (188, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false]);
      (189, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false;true]);
      (190, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;false]);
      (191, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true]);
      (192, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false;false]);
      (193, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false;true]);
      (194, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;true]);
      (195, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true]);
      (196, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;true]);
      (197, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false]);
      (198, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;false]);
      (199, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;false]);
      (200, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true;false]);
      (201, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true;true]);
      (202, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false;false]);
      (203, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;true;false]);
      (204, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;true;true]);
      (205, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false;true]);
      (206, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true]);
      (207, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;true]);
      (208, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false]);
      (209, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true;true]);
      (210, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;false]);
      (211, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false;false]);
      (212, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false;true]);
      (213, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;true]);
      (214, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true;false]);
      (215, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false]);
      (216, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false;false]);
      (217, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false;true]);
      (218, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;false]);
      (219, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;true]);
      (220, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true]);
      (221, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;true;true]);
      (222, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false;false]);
      (223, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;false;true]);
      (224, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;false]);
      (225, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true]);
      (226, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;true]);
      (227, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;false]);
      (228, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;true]);
      (229, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;true]);
      (230, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;false]);
      (231, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true]);
      (232, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;false]);
      (233, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;true]);
      (234, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;false]);
      (235, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;true]);
      (236, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false]);
      (237, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true]);
      (238, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;false]);
      (239, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false]);
      (240, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;true]);
      (241, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;false]);
      (242, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;false]);
      (243, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;true]);
      (244, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;true;true;true]);
      (245, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;false]);
      (246, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;false;true]);
      (247, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;false]);
      (248, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;false;true;true]);
      (249, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false]);
      (250, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;false]);
      (251, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;false;true]);
      (252, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;false]);
      (253, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;true]);
      (254, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false]);
      (255, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;true;true;true;false]);
      (256, [true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true])].