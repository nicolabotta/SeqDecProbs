> module FiniteSubTypeProperties

> import Data.Fin
> import Data.Vect
> import Control.Isomorphism

> import SubType
> import Finite
> import FiniteSubType
> import Decidable
> import Unique
> import SigmaOperations
> import SigmaProperties
> import VectOperations
> import VectProperties
> -- import FiniteOperations


> %default total


> ||| For decidable and unique predicates, subtypes of finite types are finite
> finiteSubTypeLemma0 : {A : Type} -> {P : A -> Type} ->
>                       Finite A -> Dec1 P -> (uP : Unique1 P) ->
>                       Finite (SubType A P uP)
> finiteSubTypeLemma0 {A} {P} fA dP uP = Evidence n iso where
>   n        : Nat
>   n        = getWitness (toVect fA dP)
>   rho      : Vect n (SubType A P uP)
>   rho      = getProof (toVect fA dP)
>   i1rho    : Injective1 rho
>   i1rho    = toVectInjective1 fA dP uP
>   i2rho    : Injective2 rho
>   i2rho    = injectiveLemma rho i1rho
>   to       : SubType A P uP -> Fin n
>   to s     = lookup s rho (toVectComplete fA dP uP s)
>   from     : Fin n -> SubType A P uP
>   from k   = index k rho
>   toFrom   : (k : Fin n) -> to (from k) = k
>   toFrom k = lookupIndexLemma k rho i2rho (toVectComplete fA dP uP (from k))
>   fromTo   : (s : SubType A P uP) -> from (to s) = s
>   fromTo s = indexLookupLemma s rho (toVectComplete fA dP uP s)
>   iso      : Iso (SubType A P uP) (Fin n)
>   iso      = MkIso to from toFrom fromTo

TODO (perhaps): get rid of dependency on Vect (stay with isos).
