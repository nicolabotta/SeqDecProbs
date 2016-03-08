> module Ops


> %default total

> %access public export


> outl  :  {A : Type} -> {P : A -> Type} -> (a : A ** P a) -> A
> outl  =  fst

> outr  :  {A : Type} -> {P : A -> Type} -> (p : (a : A ** P a)) -> P (outl p)
> outr  =  snd
