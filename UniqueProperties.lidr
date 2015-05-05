> module UniqueProperties


> import Data.Fin
> import Control.Isomorphism


> import Unique
> import Decidable
> import Finite


> %default total


> ||| Unique properties are finite
> uniqueFiniteLemma1 : {P : Type} -> P -> Unique P -> Finite P
> uniqueFiniteLemma1 {P} p uP = Evidence n (MkIso to from toFrom fromTo) where
>   n : Nat
>   n = S Z
>   to : P -> Fin n
>   to x = FZ
>   from : Fin n -> P
>   from FZ = p
>   toFrom : (k : Fin n) -> to (from k) = k
>   toFrom FZ = Refl
>   fromTo : (x : P) -> from (to x) = x
>   fromTo x = uP p x


> ||| Unique properties are finite
> uniqueFiniteLemma2 : {P : Type} -> Not P -> Unique P -> Finite P
> uniqueFiniteLemma2 {P} contra up = Evidence n (MkIso to from toFrom fromTo) where
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


> ||| Decidable and unique properties are finite
> decUniqueFiniteLemma : {P : Type} -> Dec P -> Unique P -> Finite P
> decUniqueFiniteLemma (Yes p) uP = uniqueFiniteLemma1 p uP
> decUniqueFiniteLemma (No contra) uP = uniqueFiniteLemma2 contra uP
