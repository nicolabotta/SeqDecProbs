> module NonNegRationalMeasures

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import NatPositive
> import Fraction
> import FractionNormal
 
> %default total
> %access public export
> %auto_implicits off


> ||| 
> factor : {A : Type} -> List A -> NonNegRational
> factor Nil = 1
> factor (a :: as) = fromFraction (1, Element (S (length as)) MkPositive)

> factorLemma : {A, B, C : Type} -> 
>               (as : List A) -> (f : A -> B) -> (g : A -> C) ->
>               factor (map f as) = factor (map g as)
> factorLemma  Nil f g = Refl
> factorLemma (a :: as) f g = 
>     ( factor (map f (a :: as)) )
>   ={ Refl }=
>     ( factor (f a :: map f as) )
>   ={ Refl }=
>     ( fromFraction (1, Element (S (length (map f as))) MkPositive) )
>   ={ cong {f = \ ZUZU => fromFraction (1, Element (S ZUZU) MkPositive)} (lengthLemma as f g) }=
>     ( fromFraction (1, Element (S (length (map g as))) MkPositive) )  
>   ={ Refl }=
>     ( factor (g a :: map g as) )
>   ={ Refl }=
>     ( factor (map g (a :: as)) )
>   QED


> ||| 
> average : List NonNegRational -> NonNegRational
> average xs = (sum xs) * (factor xs)


> {-

> ---}
 
