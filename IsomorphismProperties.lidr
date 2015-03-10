> module IsomorphismProperties


> import Control.Isomorphism


> %default total 


> |||
> isoEq : {A, B : Type} -> A = B -> Iso A B
> isoEq Refl = isoRefl


> |||
> isoCong : {A : Type} -> {x : A} -> {y : A} -> {P : A -> Type} -> x = y -> Iso (P x) (P y)
> isoCong {x} {P} prf = replace {P = \ z => Iso (P x) (P z)} prf isoRefl 
