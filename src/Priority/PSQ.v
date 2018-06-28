From Coq Require Import ZArith.
From Coq Require Import BinNums.
From Coq Require Import NArith.BinNat.
Open Scope N_scope.
Open Scope list_scope.

Definition Precedence := (N * Z * Z)%type.

Definition deficit_of (p:Precedence) :=
  match p with
  | (d, w, k) => d
  end.

Definition weight_of (p:Precedence) :=
  match p with
  | (d, w, k) => w
  end.

Definition key_of (p:Precedence) :=
  match p with
  | (d, w, k) => k
  end.

Definition eq_precedence (p1 p2:Precedence) : bool :=
  (deficit_of p1) =? (deficit_of p2).

Definition deficitSteps := 65536.

Definition lt_precedence (p1 p2:Precedence) : bool :=
  let d1 := deficit_of p1 in
  let d2 := deficit_of p2 in
  (d1 <? d2) && ((d2 - d1) <=? deficitSteps).


Definition deficitList : list N :=
  let idxs :=
      N.recursion nil (fun i acc => i :: acc) 256 in
  let calc w := N.div deficitSteps w in
  List.map calc idxs.

  