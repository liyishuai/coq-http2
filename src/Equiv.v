Class Equiv A :=
  { equiv : A -> A -> Prop }.

Definition eq_equiv {A B} (f : A -> B) (a1 a2 : A) :=
  f a1 = f a2.

Infix "===" := equiv (at level 70, no associativity).

Global Instance EquivPair0 {A B} `{Equiv A} `{Equiv B} : Equiv (A * B) | 0 :=
  { equiv x y := fst x === fst y /\ snd x === snd y }.

Global Instance EquivPair1 {A B} `{Equiv A} : Equiv (A * B) | 1 :=
  { equiv x y := fst x === fst y /\ snd x = snd y }.

Global Instance EquivPair2 {A B} `{Equiv B} : Equiv (A * B) | 1 :=
  { equiv x y := fst x = fst y /\ snd x === snd y }.
