> module IsomorphismProperties


> import Control.Isomorphism

> import IsomorphismOperations
> import FunProperties
> import Basics


> %default total 


> |||
> isoEq : {A, B : Type} -> A = B -> Iso A B
> isoEq Refl = isoRefl


> |||
> isoCong : {A : Type} -> {x : A} -> {y : A} -> {P : A -> Type} -> x = y -> Iso (P x) (P y)
> isoCong {x} {P} prf = replace {P = \ z => Iso (P x) (P z)} prf isoRefl 


Injectivity of to and from

> injectiveFrom : {A, B : Type} -> (iso : Iso A B) -> Injective1 (from iso)
> injectiveFrom {A} {B} (MkIso to from toFrom fromTo) b1 b2 p = s3 where
>   s1 : from b1 = from b2
>   s1 = p
>   s2 : to (from b1) = to (from b2)
>   s2 = cong s1
>   s3 : b1 = b2
>   s3 = replace2 {a = B} {a1 = to (from b1)} {a2 = b1}
>                 {b = B} {b1 = to (from b2)} {b2 = b2}
>                 {P = \ a => \b => a = b}
>                 (toFrom b1) (toFrom b2) s2
