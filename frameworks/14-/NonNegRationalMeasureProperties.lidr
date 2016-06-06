> module NonNegRationalMeasureProperties

> import Syntax.PreorderReasoning

> import NonNegRational
> import NonNegRationalMeasures
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import NonNegRationalPredicates
> import NonNegRationalLTEProperties
> import Fraction
> import FractionNormal
> import ListProperties 
> import NatPositive
 
> %default total
> %access public export
> %auto_implicits off


Properties of |factor|:

> %freeze fromFraction

> |||
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
> %freeze factorLemma


Monotonicity of |sum|, |average|:

> %thaw fromFraction

> ||| |sum| is monotone
> monotoneSum : {A : Type} ->
>               (f : A -> NonNegRational) -> (g : A -> NonNegRational) ->
>               (p : (a : A) -> f a `LTE` g a) ->
>               (as : List A) ->
>               sum (map f as) `LTE` sum (map g as) 
> monotoneSum f g p Nil = LTEZero
> monotoneSum f g p (a :: as) = s5 where
>   s1 : sum (map f (a :: as)) = f a + sum (map f as)
>   s1 = Refl
>   s2 : sum (map g (a :: as)) = g a + sum (map g as)
>   s2 = Refl
>   s3 : f a `LTE` g a
>   s3 = p a
>   s4 : sum (map f as) `LTE` sum (map g as)
>   s4 = monotoneSum f g p as
>   s5 : sum (map f (a :: as)) `LTE` sum (map g (a :: as))
>   s5 = NonNegRationalLTEProperties.monotonePlusLTE s3 s4
> %freeze monotoneSum


> ||| |average| is monotone
> monotoneAverage : {A : Type} ->
>                   (f : A -> NonNegRational) -> (g : A -> NonNegRational) ->
>                   (p : (a : A) -> f a `LTE` g a) ->
>                   (as : List A) ->
>                   average (map f as) `LTE` average (map g as) 
> monotoneAverage f g p as = monotoneMultLTE {a = sum (map f as)} 
>                                            {b = sum (map g as)} 
>                                            {c = factor (map f as)} 
>                                            {d = factor (map g as)}
>                                            s1 s3 where
>   s1 : sum (map f as) `LTE` sum (map g as)
>   s1 = monotoneSum f g p as
>   s2 : factor (map f as) `LTE` factor (map f as)
>   s2 = reflexiveLTE (factor (map f as))
>   s3 : factor (map f as) `LTE` factor (map g as)
>   s3 = replace {P = \ ZUZU => factor (map f as) `LTE` ZUZU} (factorLemma as f g) s2
> %freeze monotoneAverage


> {-

> ---}
 
