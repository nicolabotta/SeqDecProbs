> module ListOperations
> import Syntax.PreorderReasoning

> import Data.List
> import Data.List.Quantifiers
> import Sigma
> import FunOperations
> import NumRefinements

> %default total
> %access public export
> %auto_implicits on


* |List| is a functor:

> ||| fmap
> fmap : {A, B : Type} -> (A -> B) -> List A -> List B
> fmap = map


* |List| is a monad:

> ||| ret
> ret : {A : Type} -> A -> List A
> ret = pure

> ||| bind
> bind : {A, B : Type} -> List A -> (A -> List B) -> List B
> bind = (>>=)


* |List| is a container monad:

> ||| 
> NonEmpty    : {A : Type} -> List A -> Type
> NonEmpty  Nil      = Void
> NonEmpty (a :: as) = Unit

> idThere : {A : Type} -> 
>           (a : A) -> (as : List A) -> 
>           Sigma A (\ x => x `Elem` as) -> Sigma A (\ x => x `Elem` (a :: as))
> idThere a as (MkSigma x p) = MkSigma x (There p)

> ||| Tagging
> tagElem  :  {A : Type} -> (as : List A) -> List (Sigma A (\ a => a `Elem` as))
> tagElem Nil = Nil
> tagElem {A} (x :: xs) = (MkSigma x Here) :: (map (idThere x xs) (tagElem xs)) -- where
>   -- f : Sigma A (\ a => a `Elem` xs) -> Sigma A (\ a => a `Elem` (x :: xs))
>   -- f (MkSigma a p) = MkSigma a (There p)


* Show

> implementation Show (Elem a as) where
>   show = show' where
>     show' : {A : Type} -> {a : A} -> {as : List A} -> Elem a as -> String 
>     show'  Here     = "Here"
>     show' (There p) = "There" ++ show' p


* Reduction operators

> -- maxList : {A : Type} -> TotalPreorder A -> (as : List A) -> nonEmpty as -> A

> |||
> sumMapSnd : {A, B : Type} -> (Num B) => List (A, B) -> B
> sumMapSnd abs = sum (map snd abs) 

> |||
> mapIdRightMult : {A, B : Type} -> (Num B) => (List (A, B), B) -> List (A, B)
> mapIdRightMult (abs, b) = map (cross id (* b)) abs

> |||
> mvMult : {A, A', B : Type} -> (Num B) => List (A, B) -> (A -> List (A', B)) -> List (A', B)
> mvMult abs f = concat (map (mapIdRightMult . (cross f id)) abs)

> |||
> sumProds : {B : Type} -> (Num B) => List (B, B) -> B
> sumProds Nil = 0
> sumProds ((b,b') :: bbs) = b * b' + sumProds bbs 


* Ad-hoc filtering

> |||
> discardZeroes : {B : Type} -> (Num B, DecEq B) => List B -> List B
> discardZeroes  Nil      = Nil
> discardZeroes (b :: bs) with (decEq b 0)
>   | (Yes _) = discardZeroes bs
>   | (No _)  = b :: discardZeroes bs

> |||
> discardBySndZero : {A, B : Type} -> (Num B, DecEq B) => List (A, B) -> List (A, B)
> discardBySndZero  Nil      = Nil
> discardBySndZero (ab :: abs) with (decEq (snd ab) 0)
>   | (Yes _) = discardBySndZero abs
>   | (No _)  = ab :: discardBySndZero abs

