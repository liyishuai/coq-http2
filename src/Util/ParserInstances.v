(* Implementation of the [Util.Parsers] interface. *)

From Coq Require Import Vector.
From ExtLib Require Import
     Data.Nat
     Data.Monads.EitherMonad
     Data.Monads.ReaderMonad
     Data.Monads.StateMonad
     Structures.MonadExc
     Structures.Monad
     Structures.MonadTrans
     Structures.Monoid.
Import MonadNotation.
From HTTP2 Require Import
     HPACK.HPACKTypes
     Types
     Util.ByteVector
     Util.Parser
     Util.StringUtil
     Util.VectorUtil.
Import VectorNotations.

Record parser (a : Type) := mkParser {
  run_parser : stateT bytes (sum HTTP2Error) a;
                              }.
Record HPACK_parser (a : Type) := mkHPACKParser {
  run_HPACK_parser : stateT bytes (sum HPACKError) a;
                                      }.

Arguments mkParser {a}.
Arguments run_parser {a}.
Arguments mkHPACKParser {a}.
Arguments run_HPACK_parser {a}.

Instance Monad_parser : Monad parser := {
  ret _ a := mkParser (ret a);
  bind _ _ p q :=
    mkParser (run_parser p >>= fun x => run_parser (q x))%monad;
}.

Instance Monad_HPACK_parser : Monad HPACK_parser := {
  ret _ a := mkHPACKParser (ret a);
  bind _ _ p q :=
    mkHPACKParser (run_HPACK_parser p >>= fun x => run_HPACK_parser (q x))%monad;
}.

Instance MonadExc_HTTP2Error : MonadExc HTTP2Error (sum HTTP2Error) := {
  raise _ e := inl e;
  catch _ a f :=
    match a with
    | inl e => f e
    | inr v => inr v
    end;
}.

Instance MonadExc_HPACKError : MonadExc HPACKError (sum HPACKError) := {
  raise _ e := inl e;
  catch _ a f :=
    match a with
    | inl e => f e
    | inr v => inr v
    end;
}.

Instance MonadExc_parser : MonadExc HTTP2Error parser := {
  raise := fun _ e => mkParser (lift (inl e));
  catch := fun _ v h =>
             let f := (fun e => match h e with
                             | mkParser s => s
                             end) in
             match v with
             | mkParser s =>
               mkParser (catch s f)
             end;
}.

Instance MonadExc_HPACK_parser : MonadExc HPACKError HPACK_parser := {
  raise := fun _ e => mkHPACKParser (lift (inl e));
  catch := fun _ v h =>
             let f := (fun e => match h e with
                             | mkHPACKParser s => s
                             end) in
             match v with
             | mkHPACKParser s =>
               mkHPACKParser (catch s f)
             end;
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

Instance MParser_HPACK_parser : MParser byte HPACK_parser := {
  get_token := mkHPACKParser (
    s <- MonadState.get;;
    match s with
    | "" =>
      lift (inl (decodeError "not enough bytes"))
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
