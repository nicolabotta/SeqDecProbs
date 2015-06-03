> module SeqDecProbMonadicSmallTheory

> -- import Data.Fin
> -- import Data.Vect
> -- import Control.Isomorphism

> -- import Prop
> import NatProperties
> -- import SigmaOperations
> -- import SigmaProperties
> import Finite
> -- import FiniteOperations
> -- import FiniteProperties
> import Decidable
> -- import DecidableProperties
> -- import VectOperations
> -- import VectProperties
> -- import FinOperations
> -- import IsomorphismOperations


> %default total


A SDP is specified in terms of a container monad ...

> M : Type -> Type

M is a functor

> fmap  :  (a -> b) -> M a -> M b
> ret   :  a -> M a

> functorSpec1  :  fmap . id = id
> functorSpec2  :  fmap (f . g) = (fmap f) . (fmap g)

M is a monad

> bind  :  M a -> (a -> M b) -> M b
> join  :  M (M a) -> M a

> monadSpec1  :  (fmap f) . ret = ret . f
> monadSpec2  :  bind (ret a) f = f a
> monadSpec3  :  bind ma ret = ma
> monadSpec4  :  {f : a -> M b} -> {g : b -> M c} ->
>                bind (bind ma f) g = bind ma (\ x => bind (f x) g)
> monadSpec5  :  join mma = bind mma id

M is a container

> Elem  :  a -> M a -> Type
> All   :  (a -> Type) -> M a -> Type

> containerSpec1  :  Elem a (ret a)
> containerSpec2  :  Elem a ma -> Elem ma mma -> Elem a (join mma)
> containerSpec3  :  All p ma -> Elem a ma -> p a


... and, at each decision step, a set of possible states:

> X     :  (t : Nat) -> Type

... for each state, a set of options

> Y     :  (t : Nat) -> (x : X t) -> Type

and a transition function.

> step  :  (t : Nat) -> (x : X t) -> (y : Y t x) -> M (X (S t))




Predecessor relation

> Pred : X t -> X (S t) -> Type
> Pred {t} x x'  =  (y : Y t x ** x' `Elem` (step t x y))


Reachability

> Reachable : X t' -> Type
> Reachable {t' = Z}   x'  =  Unit
> Reachable {t' = S t} x'  =  (x : X t ** (Reachable x, x `Pred` x'))


Viability

> Viable : (n : Nat) -> X t -> Type
> Viable {t}  Z    x  =  Unit
> Viable {t} (S m) x  =  (y : Y t x ** All (Viable m) (step t x y))


Avoidability

> ReachableFrom : X t'' -> X t -> Type
> ReachableFrom {t'' = Z}    {t} x'' x  =  (t = Z , x = x'')
> ReachableFrom {t'' = S t'} {t} x'' x  =
>   Either  (t = S t' , x = x'') 
>           (x' : X t' ** (x' `ReachableFrom` x , x' `Pred` x''))

We can show that

> reachableFromLemma  :  (x'' : X t'') -> (x : X t) -> 
>                        x'' `ReachableFrom` x -> t'' `GTE` t

> reachableFromLemma {t'' = Z}    {t = Z}    x'' x prf =  
>   LTEZero
> reachableFromLemma {t'' = Z}    {t = S m}  x'' x (prf1 , prf2) = 
>   void (uninhabited u) where
>     u : Z = S m 
>     u = trans (sym prf1) Refl 
> reachableFromLemma {t'' = S t'} {t = Z}    x'' x prf =  
>   LTEZero
> reachableFromLemma {t'' = S t'} {t = S t'} x'' x (Left (Refl , prf2)) =  
>   eqInLTE (S t') (S t') Refl 
> reachableFromLemma {t'' = S t'} {t = t}    x'' x (Right (x' ** (prf1 , prf2))) =  
>   s3 where
>     s1  :  t' `GTE` t
>     s1  =  reachableFromLemma x' x prf1
>     s3  :  S t' `GTE` t
>     s3  =  idSuccPreservesLTE t t' s1 


> AvoidableFrom : (x' : X t') -> (x : X t) -> x' `ReachableFrom` x -> (m : Nat) -> Type
> AvoidableFrom {t'} x' x r m = 
>   (x'' : X t' ** (x'' `ReachableFrom` x , (Viable m x'' , Not (x'' = x'))))


Decidability of |Reachable|, |Viable|, |AvoidableFrom| ...


For every type (proposition) |P : Type|, |Not P| is just a synonym for
|P -> Void|

> %hide Not
> %hide Either

> namespace Decidability

>   Not : Type -> Type                                                                                                        
>   Not P = P -> Void 

A proposition |P : Type| is decidable if one can provide either a value
|p : P| or a value of type |Not P|:

>   data Either a b = Left a | Right b

>   Decidable : Type -> Type
>   Decidable P = Either P (Not P)

Thus, the question is under which conditions we can implement

< decReachable : (x : X t) -> Decidable (Reachable x)

< decViable : (n : Nat) -> (x : X t) -> Decidable (Viable n x)

> decAvoidableFrom : {t' : Nat} -> {t : Nat} -> 
>                    (x' : X t') -> (x : X t) -> (r : x' `ReachableFrom` x) -> (n : Nat) -> 
>                    Decidable (AvoidableFrom {t'} {t} x' x r n)

It turns out that four conditions are sufficient for implementing these
function (decision procedures):

Finite state space:

> fX : (t : Nat) -> Finite (X t) 

Finite control space:

> fY : (t : Nat) -> (x : X t) -> Finite (Y t x)

Decidable |Elem|:

> decElem : {t : Nat} -> (x : X t) -> (mx : M (X t)) -> Decidable (x `Elem` mx)

Decidable |All|:

> decAll : {t : Nat} -> (P : X t -> Type) -> ((x : X t) -> Decidable (P x)) -> 
>          (mx : M (X t)) -> Decidable (All P mx)

The key mechanism is

> finiteDecidableLemma : {A : Type} -> {P : A -> Type} -> 
>                        Finite A -> ((a : A) -> Decidable (P a)) -> Decidable (a : A ** P a)

With this lemma and from |fY| and decidability of |Elem| one immediately
derives decidability of |Pred|

> decPred : {t : Nat} -> (x : X t) -> (x' : X (S t)) -> Decidable (x `Pred` x')
> decPred {t} x x' = finiteDecidableLemma (fY t x) prf where
>   prf : (y : Y t x) -> Decidable (x' `Elem` (step t x y))
>   prf y = decElem x' (step t x y)

and, with

> ||| If |P| and |Q| are decidable, |(P , Q)| is decidable
> decPair : {P, Q : Type} -> Decidable P -> Decidable Q -> Decidable (P , Q)
> decPair (Left p)   (Left q)   = Left  (p , q)
> decPair (Left p)   (Right nq) = Right (\ pq => nq (snd pq))
> decPair (Right np) (Left q)   = Right (\ pq => np (fst pq))
> decPair (Right np) (Right nq) = Right (\ pq => np (fst pq))

decidability of |Reachable|:

> decReachable : {t' : Nat} -> (x' : X t') -> Decidable (Reachable x')
> decReachable {t' = Z}   x' = Left ()
> decReachable {t' = S t} x' = s1 where
>   s1 : Decidable (x : X t ** (Reachable x, x `Pred` x'))
>   s1 = finiteDecidableLemma (fX t) (\x => decPair (decReachable x) (decPred x x'))

and of |Viable|

< decViable : (n : Nat) -> (x : X t) -> Decidable (Viable n x)

> decViable : {t : Nat} -> (n : Nat) -> (x : X t) -> Decidable (Viable n x)
> decViable {t}  Z    x = Left ()
> decViable {t} (S m) x = s3 where
>   s1    :  (y : Y t x) -> Decidable (All (Viable m) (step t x y))
>   s1 y  =  decAll (Viable m) (decViable m) (step t x y)
>   s2    :  Decidable (y : Y t x ** All (Viable m) (step t x y))
>   s2    =  finiteDecidableLemma (fY t x) s1
>   s3    :  Decidable (Viable (S m) x)
>   s3    =  s2


< pps : Prob (Prob A)

