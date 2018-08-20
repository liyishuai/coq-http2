Require Import Coq.Strings.String.
Require Import ExtLib.Structures.Monads.

Inductive optionE (X:Type) : Type :=
  | Success : X -> optionE X
  | Failure : string -> optionE X.

Arguments Success {X}.
Arguments Failure {X}.

Instance Monad_optionE : Monad optionE :=
  { ret A x := Success x;
    bind A B a f := match a with
                    | Success a' => f a'
                    | Failure e => Failure e
                    end }.

Instance Exception_optionE : MonadExc string (optionE) :=
  { raise A x := Failure x;
    catch A e f := match e with
                   | Failure e => f e
                   | a => a
                   end }.