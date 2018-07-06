From HTTP2 Require Import Types.
From ExtLib Require Import Monad.

Open Scope type_scope.

Definition OptionE T := HTTP2Error + T.
Instance MonadOptionE : Monad OptionE :=
  {| ret := @inr HTTP2Error;
     bind _ _ ot f :=
       match ot with
       | inl e => inl e
       | inr t => f t
       end
  |}.
