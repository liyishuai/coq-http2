(* Implementation of the [Util.Parsers] interface. *)

From Coq Require Import Vector.
From ExtLib Require Import
     Data.Nat
     Data.Monads.EitherMonad
     Data.Monads.ReaderMonad
     Data.Monads.StateMonad
     Structures.Monad
     Structures.MonadTrans
     Structures.Monoid.
Import MonadNotation.
From HTTP2 Require Import
     Types
     Util.ByteVector
     Util.Parser
     Util.StringUtil
     Util.VectorUtil.
Import VectorNotations.

Record parser (a : Type) := mkParser {
  run_parser : stateT bytes (sum HTTP2Error) a;
}.

Arguments mkParser {a}.
Arguments run_parser {a}.

Instance Monad_parser : Monad parser := {
  ret _ a := mkParser (ret a);
  bind _ _ p q :=
    mkParser (run_parser p >>= fun x => run_parser (q x))%monad;
}.

Instance MError_parser : MError HTTP2Error parser := {
  throw _ e := mkParser (lift (inl e));
}.

Instance MParser_parser : MParser byte parser := {
  get_token := mkParser (
    s <- MonadState.get;;
    match s with
    | "" =>
      lift (inl (ConnectionError FrameSizeError "not enough bytes"))
    | c ::: s => MonadState.put s;; ret c
    end
  )%monad;
}.

Record iparser (n : nat) (a : Type) := mkIParser {
  run_iparser : ByteVector n -> a;
}.

Arguments mkIParser {n a}.
Arguments run_iparser {n a}.

Instance IMonad_iparser : IMonad_nat iparser := {
  iret _ a := mkIParser (fun _ => a);
  ibind i j _ _ p q := mkIParser (fun s =>
    let '(s1, s2) := splitAt i s in
    let x := run_iparser p s1 in
    run_iparser (q x) s2
  )%monad;
}.

Instance MParser_iparser : MParser byte (iparser 1) := {
  get_token := mkIParser (fun s =>
    match Vector_uncons s : _ * ByteVector 0 with
    | (c, _) => c
    end
  )%monad;
}.
