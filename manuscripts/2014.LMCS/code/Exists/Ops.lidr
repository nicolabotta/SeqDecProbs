> module Ops


> %default total


> outl  :  {A : Type} -> {P : A -> Type} -> (a : A ** P a) -> A
> outl  =  getWitness

> outr  :  {A : Type} -> {P : A -> Type} -> (p : (a : A ** P a)) -> P (outl p)
> outr  =  getProof
