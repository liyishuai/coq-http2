From Coq Require Import Vector.
From ExtLib Require Import
     Data.Nat
     Structures.Monad
     Structures.Monoid.
Import MonadNotation.
From HTTP2 Require Import
     Types
     Util.ByteVector
     Util.StringUtil.
Import VectorNotations.

Notation Tycon := (Type -> Type)
(only parsing).

(** * General monadic utilities *)

Definition when {m : Tycon} `{Monad m} (b : bool) (p : m unit) : m unit :=
  if b then p else ret tt.

Module MonadNotations.
Export MonadNotation.

(* Morally equivalent to [x <- f <$> c1;; c2] but explicitly
   applying [f] to the bound variable makes more information
   available to [Program Fixpoint]. *)
Notation "x <-( f ) c1 ;; c2" :=
  (bind c1 (fun _x => let x := f _x in c2))
(at level 100, f at next level, c1 at next level,
 right associativity) : monad_scope.

Notation "' pat <-( f ) c1 ;; c2" :=
  (bind c1 (fun _x => let 'pat := f _x in c2))
(at level 100, pat pattern, f at next level, c1 at next level,
 right associativity) : monad_scope.

End MonadNotations.

(** * Throwing errors *)

(* Contexts where exceptions of type [error] can be thrown. *)
Class MError (error : Type) (m : Tycon) := {
  throw : forall a, error -> m a
}.

Arguments throw {error m _ a}.

(* Throw an exception if [b = false]. *)
Definition assert {error : Type} {m : Tycon}
           `{Monad m} `{MError error m}
           (b : bool) (e : error) : m unit :=
  when (negb b)
       (throw e).

(** * Parsers *)

(* Contexts with access to a token stream. *)
Class MParser (token : Type) (m : Tycon) := {
  get_token : m token;
}.

(* Read one byte. *)
Definition get_byte {m : Tycon} `{MParser byte m} : m byte :=
  get_token.

(* Read [n] bytes. *)
Fixpoint get_bytes {m : Tycon} `{Monad m} `{MParser byte m}
         (n : nat) : m bytes :=
  match n with
  | O => ret ""
  | S n =>
    b <- get_byte;;
    bs <- get_bytes n;;
    ret (b ::: bs)
  end%monad.

(* Read [n] bytes into a sized [ByteVector]. *)
Fixpoint get_vec {m : Tycon} `{Monad m} `{MParser byte m}
         (n : nat) : m (ByteVector n) :=
  match n with
  | O => ret []
  | S n =>
    b <- get_byte;;
    bs <- get_vec n;;
    ret (b :: bs)
  end%monad.

(* * Indexed monads *)

(* A generalization of monads where the context [m] is indexed
   by monoidal values (here, natural numbers). *)
Polymorphic Class IMonad {ix : Type} (Mix : Monoid ix) (m : ix -> Tycon) := {
  iret : forall (a : Type), a -> m (monoid_unit Mix) a;
  ibind : forall (i j : ix) (a b : Type),
      m i a -> (a -> m j b) -> m (monoid_plus Mix i j) b;
}.

Arguments iret {ix Mix m _ a}.
Arguments ibind {ix Mix m _ i j a b}.

(* [Program] seems to get confused if definitions are not
   wrapped in [icast]. *)
Definition icast_ : forall ix (m : ix -> Tycon) (i j : ix) a,
    i = j -> m i a -> m j a.
Proof. intros; subst; auto. Qed.

Arguments icast_ {ix m i j a}.
Notation icast := (icast_ _).

Notation IMonad_nat := (IMonad Monoid_nat_plus).

(* Transform a monad to an indexed one, ignoring the parameter. *)
Polymorphic Definition indexed (m : Tycon) (n : nat) := m.

Polymorphic Instance IMonad_indexed {m : Tycon} `{Monad m} :
  IMonad_nat (indexed m) := {
  iret _ a := ret a;
  ibind _ _ _ _ p q := bind p q;
}.

Polymorphic Definition unindex {m n a} : indexed m n a -> m a :=
  fun p => p.

(* Indexed monads use the same syntax as monads. *)
Module Import IMonadNotations.

Delimit Scope imonad_scope with imonad.

Notation "x <- c1 ;; c2" := (ibind c1 (fun x => c2))
(at level 100, c1 at next level, right associativity) : imonad_scope.

Notation "x <-( f ) c1 ;; c2" :=
  (ibind c1 (fun _x => let x := f _x in c2))
(at level 100, f at next level, c1 at next level,
 right associativity) : imonad_scope.

Notation "e1 ;; e2" := (_ <- e1 ;; e2)%imonad
(at level 100, right associativity) : imonad_scope.

Notation "' pat <- c1 ;; c2" := (ibind c1 (fun pat => c2))
(at level 100, pat pattern, c1 at next level, right associativity) : imonad_scope.

Notation "' pat <-( f ) c1 ;; c2" :=
  (ibind c1 (fun _x => let 'pat := f _x in c2))
(at level 100, pat pattern, f at next level, c1 at next level,
 right associativity) : imonad_scope.

End IMonadNotations.

(* Read [n] bytes into a sized [ByteVector], also
   indexing the parser with the length [n]. *)
Program Fixpoint iget_vec {m : nat -> Tycon}
         `{IMonad_nat m} `{MParser byte (m 1%nat)}
         (n : nat) : m n (ByteVector n) :=
  match n with
  | O => iret []
  | S n =>
    icast (
      b <- (get_byte : m 1%nat _);;
      bs <- iget_vec n;;
      iret (b :: bs))
  end%imonad.
