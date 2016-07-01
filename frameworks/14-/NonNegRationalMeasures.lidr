> module NonNegRationalMeasures

> import Syntax.PreorderReasoning

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import NatPositive
> import Fraction
> import FractionNormal
> import FractionPredicates --
> import FractionProperties --
 
> %default total
> %access public export
> %auto_implicits off


> ||| 
> factor : {A : Type} -> List A -> NonNegRational
> factor Nil = 1
> factor (a :: as) = fromFraction (1, Element (S (length as)) MkPositive)

> ||| The sum of n terms of the form 1/(S m) is n/(S m)
> lala : (n : Nat) -> (m : Nat ) -> 
>        sum (replicate n (fromFraction (1, Element (S m) MkPositive))) = fromFraction (n, Element (S m) MkPositive)
> lala Z m =
>   let zeroOverOne = (0, Element 1 MkPositive) in
>   let zeroOverSm  = (0, Element (S m) MkPositive) in
>   let oneOverSm   = (1, Element (S m) MkPositive) in
>     ( sum (replicate Z (fromFraction oneOverSm)) )
>   ={ Refl }=
>     ( sum Nil )
>   ={ Refl }=
>     ( fromFraction zeroOverOne )
>   ={ fromFractionEqLemma zeroOverOne zeroOverSm Refl }=
>     ( fromFraction zeroOverSm )
>   QED
> lala (S n) m =
>   let Sm' = Element (S m) MkPositive in
>   let Sm  = toNat Sm' in
>   let Sn  = S n in 
>     ( sum (replicate (S n) (fromFraction (1, Sm'))) )
>   ={ Refl }=
>     ( sum (fromFraction (1, Sm') :: replicate n (fromFraction (1, Sm'))) )
>   ={ Refl }=
>     ( fromFraction (1, Sm') + sum (replicate n (fromFraction (1, Sm'))) )
>   ={ cong (lala n m) }=
>     ( fromFraction (1, Sm') + fromFraction (n, Sm') )
>   ={ fromFractionLinear (1, Sm') (n, Sm') }=
>     ( fromFraction ((1, Sm') + (n, Sm')) )
>   ={ Refl }=
>     ( fromFraction (1 * Sm + n * Sm, Sm' * Sm') )
>   ={ cong (sym (multDistributesOverPlusLeft 1 n Sm)) }=
>     ( fromFraction ((1 + n) * Sm, Sm' * Sm') )
>   ={ multElimRight (1 + n) Sm' Sm' }=
>     ( fromFraction (1 + n, Sm') )      
>   ={ cong (plusOneSucc n) }=
>     ( fromFraction (Sn, Sm') )
>   QED


> ||| 
> average : List NonNegRational -> NonNegRational
> average xs = (sum xs) * (factor xs)


> {-

> ---}
 
