> module Finite
> import Prelude.Maybe
> import Data.Fin
> import Control.Isomorphism
> import EmbProj
> 
> %default total 


> ||| Notion of finiteness for types
> Finite : Type -> Type
> Finite A = Exists (\ n => Iso A (Fin n))

> Finite0 : Type -> Type
> Finite0 = Finite

> Finite1 : {A : Type} -> (P : A -> Type) -> Type
> Finite1 {A} P = (a : A) -> Finite0 (P a) 


This definition requires an exact cardinality |n| which may be
difficult to compute. But it is enough to know a finite bound, so an
alternative definition which may be more convenient is the following:

> FiniteSub : Type -> Type
> FiniteSub A = Exists (\ n => EmbProj A (Fin n))

----------------

> FiniteN : Nat -> Type -> Type
> FiniteN n A = Iso A (Fin n)
