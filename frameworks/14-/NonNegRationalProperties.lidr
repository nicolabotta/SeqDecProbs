> module NonNegRationalProperties


> import Syntax.PreorderReasoning

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import NonNegRationalPredicates
> import NonNegRationalLTEProperties
> import Fraction
> import FractionNormal
> -- import NatPositive
> import ListProperties 
 
> %default total
> %access public export


Properties of |sum|, |average|:

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
> %freeze factorLemma


> ||| 
> average : List NonNegRational -> NonNegRational
> average xs = (sum xs) * (factor xs)


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


> {-

> ---}
 
