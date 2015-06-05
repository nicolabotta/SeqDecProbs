> module SimpleProb1

> import Data.Vect
> import Data.So

> import Vect.Ops
> import Util.VectExtensions1
> import Float.Float


> data SimpleProb : Type -> Type where
>   SP : (aps : Vect n (alpha, NonNegFloat)) -> 
>        So (foldl (+) 0.0 (map (cast . snd) aps) == 1.0) ->
>        SimpleProb alpha


> suppBy : (alpha -> alpha -> Bool) -> 
>          SimpleProb alpha -> 
>          (n : Nat ** Vect n alpha) 
> suppBy {alpha} p (SP aps _) = nubBy p (getProof as) where
>  as : (n : Nat ** Vect n alpha) 
>  as = mapFilter fst notz aps where
>    notz : (alpha, NonNegFloat) -> Bool
>    notz (_, MkNonNegFloat px _) = px /= 0.0


> supp : Eq alpha =>
>        SimpleProb alpha -> 
>        (n : Nat ** Vect n alpha) 
> supp = suppBy (==)


> normalizeBy : (alpha -> alpha -> Bool) -> 
>               SimpleProb alpha -> 
>               SimpleProb alpha
> normalizeBy {alpha} p (SP aps q) = SP (getProof aps') q' where
>   f : alpha -> (alpha, NonNegFloat)
>   f a = (a, foldl g (MkNonNegFloat 0.0 Oh) aps) where
>     g : NonNegFloat -> (alpha, NonNegFloat) -> NonNegFloat
>     g (MkNonNegFloat e prf) (b, (MkNonNegFloat pb _)) = 
>       if (p a b)
>       then (MkNonNegFloat (e + pb) (believe_me Oh))
>       else (MkNonNegFloat e prf)
>   aps' : (n : Nat ** Vect n (alpha, NonNegFloat))
>   aps' = fmap f (suppBy p (SP aps q))
>   q' : So (foldl (+) 0.0 (map (cast . snd) (getProof aps')) == 1.0)
>   q' = believe_me Oh


> normalize : Eq alpha => SimpleProb alpha -> SimpleProb alpha
> normalize = normalizeBy (==)


