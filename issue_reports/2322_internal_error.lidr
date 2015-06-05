> import Data.So
> import Data.Vect

> %default total

> data NonNegFloat : Type where
>   MkNonNegFloat : (x : Float) -> So (x >= 0.0) -> NonNegFloat

> instance Cast NonNegFloat Float where
>   cast (MkNonNegFloat x _) = x

> isComponentwiseLE : (Ord alpha) => Vect n alpha -> Vect n alpha -> Bool
> isComponentwiseLE Nil _ = True
> isComponentwiseLE (x :: xs) (y :: ys) = (x <= y) && isComponentwiseLE xs ys

> NNF_minus_F : (x : Vect n NonNegFloat) ->
>               (y : Vect n Float) ->
>               So (isComponentwiseLE y (map cast x)) ->
>               Vect n NonNegFloat
> NNF_minus_F Nil                         _         _ = Nil
> NNF_minus_F ((MkNonNegFloat x _) :: xs) (y :: ys) p = (MkNonNegFloat (x - y) (believe_me Oh)) :: (NNF_minus_F xs ys ?p') -- where
>   -- z : NonNegFloat
>   -- z = (x - y ** believe_me Oh)


