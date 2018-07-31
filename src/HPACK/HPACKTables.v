From HTTP2.HPACK Require Import HPACKTypes HPACKEncode.
From HTTP2 Require Import Types Util.Parser.
From Coq Require Import Strings.String BinNat Lists.List Basics.
From ExtLib Require Import Monad.
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
Definition index_into_tables {m:Tycon} `{Monad m} `{MError HPACKError m} (i:N)
           (dynamic_table:DTable) : m HeaderField :=
  if i =? 0 then throw (processError "0 is an invalid index")
  else if i <=? N.of_nat (length static_table)
       then opt_err (processError "Index not in static table")
                    (nth_error static_table (N.to_nat i))
       else opt_err (processError "Index not in dynamic table")
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

Definition find_table {m:Tycon} `{Monad m} `{MError HPACKError m}
           (h:HeaderField) (dynamic_table:DTable) : m N :=
  match (find_table_h h static_table) with
  | None =>
    match (find_table_h h (snd dynamic_table)) with
    | None => throw (processError "Header Field not in any table")
    | Some x => ret (x + N.of_nat (length static_table))
    end
  | Some x => ret x
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
Program Fixpoint dtable_entry_eviction (dynamic_table:DTable)
        {measure (length (snd dynamic_table))}: DTable :=
  match size_dtable dynamic_table <=? fst dynamic_table with
  | true => dynamic_table
  | false => dtable_entry_eviction (fst dynamic_table,
                                   removelast (snd dynamic_table))
  end.
Obligation 1.
  symmetry in Heq_anonymous; rewrite N.leb_gt in Heq_anonymous.
  specialize exists_last with (l:=snd dynamic_table); intros exists_last.
  destruct dynamic_table; destruct t.
  - simpl in *. compute in Heq_anonymous; destruct n; inversion Heq_anonymous.
  - cut (snd (n, h :: t) <> []); intros; try solve [simpl; congruence].
    apply exists_last in H. inversion H. inversion H0. rewrite H1.
    rewrite removelast_app; try congruence. simpl. repeat rewrite app_length.
    simpl. rewrite PeanoNat.Nat.add_0_r. rewrite PeanoNat.Nat.add_1_r.
    apply PeanoNat.Nat.lt_succ_diag_r.
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