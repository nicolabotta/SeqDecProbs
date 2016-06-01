> module UniqueProperties


> import Data.Fin
> import Control.Isomorphism


> import Unique
> import Decidable
> import Finite
> import Sigma
> import PairsOperations

> %default total

> %access public export


> |||
> uniqueLemma : {A : Type} -> {P : A -> Type} -> ((a : A) -> Unique (P a)) ->
>               (a1 : A) -> (a2 : A) -> (pa1 : P a1) -> (pa2 : P a2) -> 
>               (a1 = a2) -> pa1 = pa2
> uniqueLemma {A} {P} prf a a pa1 pa2 Refl = prf a pa1 pa2
> %freeze uniqueLemma


> ||| Unique properties are finite
> uniqueFiniteLemma1 : {P : Type} -> P -> Unique P -> Finite P
> uniqueFiniteLemma1 {P} p uP = MkSigma n (MkIso to from toFrom fromTo) where
>   n : Nat
>   n = S Z
>   to : P -> Fin n
>   to x = FZ
>   from : Fin n -> P
>   from FZ = p
>   from (FS k) = absurd k
>   toFrom : (k : Fin n) -> to (from k) = k
>   toFrom FZ = Refl
>   toFrom (FS k) = absurd k
>   fromTo : (x : P) -> from (to x) = x
>   fromTo x = uP p x
> %freeze uniqueFiniteLemma1


> ||| Unique properties are finite
> uniqueFiniteLemma2 : {P : Type} -> Not P -> Finite P
> uniqueFiniteLemma2 {P} contra = MkSigma n (MkIso to from toFrom fromTo) where
>   n : Nat
>   n = Z
>   to : P -> Fin n
>   to x = void (contra x)
>   from : Fin n -> P
>   from k = absurd k
>   toFrom : (k : Fin n) -> to (from k) = k
>   toFrom k = absurd k
>   fromTo : (x : P) -> from (to x) = x
>   fromTo x = void (contra x)
> %freeze uniqueFiniteLemma2


> ||| Decidable and unique properties are finite
> decUniqueFiniteLemma : {P : Type} -> Dec P -> Unique P -> Finite P
> decUniqueFiniteLemma (Yes p)     uP = uniqueFiniteLemma1 p uP
> decUniqueFiniteLemma (No contra) _ = uniqueFiniteLemma2 contra
> %freeze decUniqueFiniteLemma


> {-

> ---}
