> module Ops


> %default total


> outl : {a : Type} -> {P : a -> Type} -> Sigma a P -> a
> outl = getWitness

> outr : {a : Type} -> {P : a -> Type} -> (s : Sigma a P) -> P (getWitness s)
> outr = getProof
