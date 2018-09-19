From ExtLib.Data Require Import Monads.EitherMonad.
From ExtLib.Structures Require Import Monad.

From SimpleIO Require Import IOMonad CoqPervasives.

From HTTP2.Util Require Import StringUtil Parser.

Inductive file_parser (A : Type) : Type :=
| FileParser : (in_channel -> IO A) -> file_parser A
.

Arguments FileParser {A}.

Definition run_file_parser {A : Type} (fp : file_parser A) :
  in_channel -> IO A :=
  match fp with
  | FileParser f => f
  end.

Instance Monad_file_parser : Monad file_parser := {
  ret _ a := FileParser (fun _ => IOMonad.ret a);
  bind _ _ m k := FileParser (fun h =>
    IOMonad.bind (run_file_parser m h) (fun x =>
    run_file_parser (k x) h));
}.

Instance MParser_file_parser : MParser byte file_parser := {
  get_token := FileParser (fun h =>
    IOMonad.map_io ascii_of_char (input_char h))
}.

Instance MParser_eitherT (m : Tycon) token e
         `{Monad m} `{MParser token m} :
  MParser token (eitherT e m) := {
    get_token := mkEitherT _ _ _
      (liftM inr get_token : m (e + token)%type);
  }.
