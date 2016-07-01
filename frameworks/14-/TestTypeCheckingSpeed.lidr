> import Syntax.PreorderReasoning

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import NatPositive
> import Fraction
> import FractionNormal
> import FractionPredicates
> import FractionBasicProperties
> import PNat
> import PNatOperations
> import PNatProperties
 
> %default total
> %access public export
> %auto_implicits off


> ||| The sum of n terms of the form 1/(S m) is n/(S m)
> lala : (n : Nat) -> (m : Nat ) -> 
>        sum (replicate n (fromFraction (1, Element (S m) MkPositive))) = fromFraction (n, Element (S m) MkPositive)

> lala Z m =
>   let Sm' = Element (S m) MkPositive in
>   let SZ' = Element 1 MkPositive in
>     ( sum (replicate Z (fromFraction (1, Sm'))) )
>   ={ Refl }=
>     ( sum Nil )
>   ={ Refl }=
>     ( fromFraction (0, SZ') )
>   ={ fromFractionEqLemma (0, SZ') (0, Sm') Refl }=
>     ( fromFraction (0, Sm') )
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
