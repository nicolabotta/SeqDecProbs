> module FinProperties

> import Data.Fin
> import Data.Vect

> import FunProperties
> import FinOperations
> import NatProperties
> import Basics


> %default total


> -- %hide Prelude.List.tail
> -- %hide Prelude.Stream.tail
> -- %hide Data.VectType.Vect.tail


|Fin 0| properties:

> fin0Lemma : (i : Fin Z) -> (j : Fin Z) -> i = j 
> fin0Lemma i j = absurd i


|Fin 1| properties:

> fin1Lemma : (i : Fin (S Z)) -> (j : Fin (S Z)) -> i = j 
> fin1Lemma FZ      FZ    = Refl
> fin1Lemma FZ     (FS k) = absurd k
> fin1Lemma (FS k)  FZ    = absurd k
> fin1Lemma (FS k) (FS j) = absurd k


Injectivity of FS

> ||| FS is injective (one direction)
> fsInjective1 : (left : Fin n) -> (right : Fin n) -> FS left = FS right -> left = right
> fsInjective1 = FSInjective  


> ||| FS is injective (the other way round)
> fsInjective2 : (left : Fin n) -> (right : Fin n) -> Not (left = right) -> Not (FS left = FS right)
> -- fsInjective2 left right contra = contra . (FSInjective left right)
> fsInjective2 = injectiveLemma FS fsInjective1


> ||| FS preserves equality
> fsPreservesEq : (left : Fin n) -> (right : Fin n) -> left = right -> FS left = FS right
> fsPreservesEq left right = cong




|finToNat| properties:

> ||| |finToNat (k : Fin n)| is LT bounded by |n| 
> finToNatLemma : {n : Nat} -> (k : Fin n) -> LT (finToNat k) n 
> finToNatLemma {n = Z}   k       =  absurd k
> finToNatLemma {n = S m} FZ      =  LTESucc LTEZero 
> finToNatLemma {n = S m} (FS k)  =  LTESucc (finToNatLemma k) 


|weaken| properties:

> weakenPreservesEq : (i : Fin n) -> (j : Fin n) -> (i = j) -> (weaken i = weaken j)
> weakenPreservesEq left _ Refl = Refl

> weakenInjective : (i : Fin n) -> (j : Fin n) -> (weaken i = weaken j) -> (i = j)
> weakenInjective  FZ     FZ    Refl = Refl
> weakenInjective  FZ    (FS k) Refl impossible
> weakenInjective (FS k)  FZ    Refl impossible
> weakenInjective (FS k) (FS j) prf = s5 where
>   s1 : weaken (FS k) = weaken (FS j)
>   s1 = prf
>   s2 : FS (weaken k) = FS (weaken j)
>   s2 = s1
>   s3 : weaken k = weaken j
>   s3 = FSInjective (weaken k) (weaken j) s2
>   s4 : k = j
>   s4 = weakenInjective k j s3
>   s5 : FS k = FS j
>   s5 = cong s4

> notWeakenLemma : (i : Fin n) -> (j : Fin n) -> Not (i = j) -> Not (weaken i = weaken j)
> notWeakenLemma i j contra = \ prf => contra (weakenInjective i j prf)


|tail| properties:

> tailSuccLemma : {A : Type} -> (f : Fin (S n) -> A) -> (i : Fin n) -> (tail f) i = f (FS i)
> tailSuccLemma f i = Refl 

> tailSuccEqLemma : {n : Nat} -> {A : Type} -> 
>                   (i : Fin n) -> (j : Fin n) -> (f : Fin (S n) -> A) -> 
>                   (tail f) i = (tail f) j -> 
>                   f (FS i) = f (FS j)
> tailSuccEqLemma i j f prf = replace2 (tailSuccLemma f i) (tailSuccLemma f j) prf


|toVect| properties:

> ||| |toVect| representations of finite functions are complete
> toVectComplete : {n : Nat} -> {A : Type} -> (f : Fin n -> A) -> (k : Fin n) -> Elem (f k) (toVect f)
> toVectComplete {n = Z} _  k     = void (uninhabited k)
> toVectComplete         f  FZ    = Here
> toVectComplete         f (FS j) = There (toVectComplete (tail f) j)


> toVectRepr : {A : Type} -> (f : Fin n -> A) -> (k : Fin n) -> index k (toVect f) = f k
> toVectRepr {n = Z}   f k  = absurd k
> toVectRepr {n = S m} f FZ     = Refl
> toVectRepr {n = S m} f (FS k) = toVectRepr (tail f) k
