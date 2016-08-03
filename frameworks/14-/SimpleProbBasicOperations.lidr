> module SimpleProbBasicOperations

> import Data.List
> import Syntax.PreorderReasoning

> import SimpleProb
> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import NonNegRationalMeasureProperties
> import NatPositive
> import Fraction
> import FractionNormal
> import FractionPredicates
> import NumRefinements
> import FunOperations
> import ListOperations
> import ListProperties

> %default total
> %access public export
> %auto_implicits off


> |||
> toList : {A : Type} -> SimpleProb A -> List (A, NonNegRational)
> toList (MkSimpleProb aps _) = aps


> |||
> normalize : {A : Type} -> SimpleProb A -> SimpleProb A
> {-
> normalize {A} (MkSimpleProb aps sum) = MkSimpleProb aps' sum' where
>   aps' : List (A, NonNegRational)
>   aps' = discardBySndZero aps
>   sum' : sumMapSnd aps' = 1
>   sum' = trans (discardBySndZeroLemma aps) sum
> -}
> normalize {A} (MkSimpleProb Nil sum) = MkSimpleProb Nil sum
> normalize {A} (MkSimpleProb (ap :: Nil) sum) = MkSimpleProb (ap :: Nil) sum
> normalize {A} (MkSimpleProb (ap :: ap' :: aps) sum) = MkSimpleProb aps' sum' where
>   aps' : List (A, NonNegRational)
>   aps' = discardBySndZero (ap :: ap' :: aps)
>   sum' : sumMapSnd aps' = 1
>   sum' = trans (discardBySndZeroLemma (ap :: ap' :: aps)) sum


> |||
> support : {A : Type} -> SimpleProb A -> List A
> support sp = map fst (toList (normalize sp))


> |||
> probs : {A : Type} -> SimpleProb A -> List NonNegRational
> probs sp = map snd (toList (normalize sp))


> ||| 'prob sp a' is the probability of 'a' according to 'sp'
> prob : {A : Type} -> (Eq A) => SimpleProb A -> A -> NonNegRational
> prob (MkSimpleProb aps _) a = foldr f 0 aps where
>   f : (A, NonNegRational) -> NonNegRational -> NonNegRational
>   f (a', p') p = if (a == a') then p + p' else p


> ||| Make a SimpleProb in which all elements of a list have the same 
> ||| probablility. If the list has no duplicates, this results in a
> ||| uniform probability distribution
> mkSimpleProb : {A : Type} -> (as : List A) -> ListOperations.NonEmpty as -> SimpleProb A
> mkSimpleProb      Nil      prf = absurd prf
> mkSimpleProb {A} (a :: as) _   = MkSimpleProb aps s1p where
>   m : Nat
>   m = length as
>   ps : List NonNegRational
>   ps = replicate (S m) (fromFraction (1, Element (S m) MkPositive))
>   sps : sum ps = fromFraction (S m, Element (S m) MkPositive)
>   sps = sumLemma0 (S m) m
>   aps : List (A, NonNegRational)
>   aps = zip (a :: as) ps
>   leq : length (a :: as) = length ps
>   leq = ( length (a :: as) )
>       ={ Refl }=
>         ( S (length as) )
>       ={ Refl }=
>         ( S m )
>       ={ sym (lengthReplicateLemma (S m) (fromFraction (1, Element (S m) MkPositive))) }=
>         ( length (replicate (S m) (fromFraction (1, Element (S m) MkPositive))) )
>       ={ Refl }=
>         ( length ps )
>       QED  
>   s1p : sumMapSnd aps = 1
>   s1p = ( sumMapSnd aps )
>       ={ sumMapSndUnzipLemma aps }=
>         ( sum (snd (unzip aps)) )
>       ={ Refl }=
>         ( sum (snd (unzip (zip (a :: as) ps))) )
>       ={ cong {f = sum . snd} (unzipZipLemma (a :: as) ps leq) }=
>         ( sum (snd ((a :: as), ps)) )
>       ={ cong {f = sum} Refl }=
>         ( sum ps )
>       ={ sps }=
>         ( fromFraction (S m, Element (S m) MkPositive) )
>       ={ fromFractionEqLemma (S m, Element (S m) MkPositive) (S Z, Element (S Z) MkPositive) (multCommutative (S m) (S Z)) }=
>         ( fromFraction (S Z, Element (S Z) MkPositive) )
>       ={ Refl }=
>         ( 1 )
>       QED






> {-

> prob : {A : Type} -> (DecEq A) => SimpleProb A -> A -> NonNegRational
> prob {A} (MkSimpleProb aps _) a = foldr f 0 aps where
>   f : (A, NonNegRational) -> NonNegRational -> NonNegRational
>   f (a', p') p with (decEq a a') 
>     | (Yes _) = p + p' 
>     | (No _)  = p

> ---}    

