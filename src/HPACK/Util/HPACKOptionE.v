From HTTP2.HPACK Require Import HPACKTypes.
From ExtLib Require Import Monad.

Open Scope type_scope.

Definition OptionE T := HPACKError + T.
Instance MonadOptionE : Monad OptionE :=
  {| ret := @inr HPACKError;
     bind _ _ ot f :=
       match ot with
       | inl e => inl e
       | inr t => f t
       end
  |}.

Definition err {T} (e:HPACKError) (o:option T) : OptionE T :=
  match o with
  | None => inl e
  | Some v => ret v
  end.

Definition perr {T} (o:option T) : OptionE T := err processError o.
Definition eerr {T} (o:option T) : OptionE T := err encodeError o.
Definition derr {T} (o:option T) : OptionE T := err decodeError o.

Definition try_catch {T} (o:OptionE T) (f: T -> OptionE T)
           (g: HPACKError -> OptionE T) : OptionE T :=
  match o with
  | inl e => g e
  | inr t => f t
  end.

Definition try_catch_r {T} (o:OptionE T) (g:HPACKError -> OptionE T) : OptionE T :=
  try_catch o ret g.
Definition try_catch_l {T} (o:OptionE T) (f: T -> OptionE T) : OptionE T :=
  try_catch o f inl.

Definition fmap {T1 T2} (o:OptionE T1) (f: T1 -> OptionE T2) : OptionE T2 :=
  match o with
  | inr v => f v
  | inl e => inl e
  end.
             