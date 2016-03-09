> module ExistsOperations


> import PairsOperations


> %default total

> %access public export


> |||
> outl : {A : Type} -> {P : A -> Type} -> Exists {a = A} P -> A
> outl = getWitness


> |||
> outr : {A : Type} -> {P : A -> Type} -> (s : Exists {a = A} P) -> P (outl s)
> outr = getProof


