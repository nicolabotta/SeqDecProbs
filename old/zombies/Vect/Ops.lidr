> module Ops


> import Data.So
> import Data.Fin

> import BoundedNat.Blt
> import Nat.Postulates
> import Nat.Properties
> import Float.Float

> import Syntax.PreorderReasoning

> %default total


> nubbedBy : (alpha -> alpha -> Bool) -> Vect n alpha -> Bool
> nubbedBy {n} p v = n == (getWitness (nubBy p v))

> idx : Vect n alpha -> Blt n -> alpha
> idx {n = Z} Nil b = void (ltZ_bot (getProof b))
> idx (a :: as) (Z ** _) = a
> idx {n = S m} (a :: as) (S k ** q) = idx {n = m} as (k ** lemma5  q)

> idx1 : Vect n alpha -> Blt n -> alpha
> idx1 = idx

> idx2 : Vect m (Vect n alpha) -> 
>        (i : Blt m) -> 
>        (j : Blt n) -> 
>        alpha
> idx2 xss i j = idx1 (idx1 xss i) j


> xdi : (p : alpha -> alpha -> Bool) ->
>       (a : alpha) ->
>       (as : Vect n alpha) -> 
>       So (elemBy p a as) ->
>       Blt n
> xdi p a as q = (fromMaybe Z m ** believe_me Oh) where
>   m : Maybe Nat
>   m = map finToNat (findIndex (p a) as)


> modifyVect : Vect n alpha -> (Blt n, alpha) -> Vect n alpha
> modifyVect {n = Z} Nil (b, _) = void (ltZ_bot (getProof b))
> modifyVect (a :: as) ((Z  ** _), a') = a' :: as
> modifyVect {n = S m} (a :: as) ((S k ** q), a')
>             = a :: (modifyVect {n = m} as ((k ** lemma5 q), a'))

> modifyVectLemma0 : {n : Nat} -> 
>                    {i : Blt n} -> 
>                    {ss : Vect n alpha} -> 
>                    modifyVect ss (i, idx ss i) = ss
>
> modifyVectLemma0 {n = Z} {i = i} {ss = ss} = BltLemma0 i 
> 
> modifyVectLemma0 {n = S n} {i = (Z ** Oh)} {ss = s :: ss} = 
>
>   (modifyVect (s :: ss) ((Z ** Oh), idx (s :: ss) (Z ** Oh))) 
>
>   ={ Refl }=
>
>   (modifyVect (s :: ss) ((Z ** Oh), s)) 
>
>   ={ Refl }=
>
>   (s :: ss) 
>   QED
>
> modifyVectLemma0 {n = S m} {i = (S j ** p)} {ss = s :: ss} = 
>
>   (modifyVect (s :: ss) ((S j ** p), idx (s :: ss) (S j ** p))) 
>
>   ={ Refl }=
>
>   (modifyVect (s :: ss) ((S j ** p), idx ss (j ** lemma5 p)))
>
>   ={ Refl }=
>
>   (s :: modifyVect ss ((j ** lemma5 p), idx ss (j ** lemma5 p)))
>
>   ={ (cong {f = \ x => s :: x} (modifyVectLemma0 {n = m} {i = (j ** lemma5 p)})) }=
>
>   (s :: ss)
>
>   QED

> isComponentwiseLE : (Ord alpha) => Vect n alpha -> Vect n alpha -> Bool
> isComponentwiseLE Nil _ = True
> isComponentwiseLE (x :: xs) (y :: ys) = 
>   (x <= y) && isComponentwiseLE xs ys

> NNF_minus_F : (x : Vect n NonNegFloat) ->
>               (y : Vect n Float) ->
>               So (isComponentwiseLE y (map cast x)) ->
>               Vect n NonNegFloat
> NNF_minus_F Nil _ _ = Nil
> NNF_minus_F ((MkNonNegFloat x p) :: xs) (y :: ys) _ = 
>   (MkNonNegFloat (x - y) (believe_me Oh)) :: 
>   (NNF_minus_F xs ys (believe_me Oh))



