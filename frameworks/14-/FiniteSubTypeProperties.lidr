> module FiniteSubTypeProperties

> import Data.Fin
> import Data.Vect
> import Control.Isomorphism

> import SubType
> import Finite
> import FiniteSubType
> import Decidable
> import Unique
> import UniqueProperties
> import SigmaProperties


> %default total

> %access public export


> ||| For decidable and unique predicates, subtypes of finite types are finite
> ||| (proof suggested my Matteo Acerbi)
> finiteSubTypeLemma0 : {A : Type} -> {P : A -> Type} ->
>                       Finite A -> Dec1 P -> (uP : Unique1 P) ->
>                       Finite (SubType A P uP)
> finiteSubTypeLemma0 fA dP uP = finiteSigmaLemma0 fA (\ a => decUniqueFiniteLemma (dP a) (uP a))
> %freeze finiteSubTypeLemma0 -- frozen

