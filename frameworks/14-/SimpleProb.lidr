> module SimpleProb

> import Data.So
> import Data.Fin
> import Data.Vect

> %default total 


> data SimpleProb : Type -> Type where
>   MkSimpleProb : (as : Vect n alpha) -> 
>                  (ps : Vect n Float) ->
>                  ((k : Fin n) -> So (index k ps >= 0.0)) ->
>                  sum ps = 1.0 -> 
>                  SimpleProb alpha 


Vect operations

> asFun : {A : Type} -> Vect n A -> (Fin n -> A)
> asFun v k = index k v

> sum' : Vect m Nat -> Nat
> sum' Nil = Z
> sum' (n :: ns) = n + sum' ns

> concat' : {A : Type} -> 
>           (nass : Vect m (n : Nat ** Vect n A)) -> 
>           Vect (sum' (map getWitness nass)) A
> concat' Nil = Nil
> concat' ((n ** as) :: nass) = as ++ concat' nass

> Coprime : Nat -> Nat -> Type
> Coprime m n = gcd m n = S Z

> data NonNegQ  :  Type where
>   MkNonNegQ  :  (m : Nat) -> (n : Nat) -> Not (n = Z) -> Coprime m n -> NonNegQ

> instance Show NonNegQ where
>   show (MkNonNegQ m n p q) = "frac " ++ show m ++ " " ++ show n

> numerator : NonNegQ -> Nat
> numerator (MkNonNegQ m n p q) = m 

> denominator : NonNegQ -> Nat
> denominator (MkNonNegQ m n p q) = n

> succNotZ : Not (S n = Z)

> lcmLemma1 : Not (m = Z) -> Not (n = Z) -> Not (lcm m n = Z)

> -- gcdLemma1 : gcd () () = S Z

> plusQ : NonNegQ -> NonNegQ -> NonNegQ
> plusQ (MkNonNegQ m1 n1 p1 q1) (MkNonNegQ m2 n2 p2 q2) = MkNonNegQ m n p q where
>   n   : Nat
>   n   = lcm n1 n2
>   p   : Not (n = Z)
>   p   = lcmLemma1 p1 p2
>   m   : Nat
>   m   = m1 * (divNatNZ n1 n p) + m2 * (divNatNZ n2 n p)
>   q   : Coprime m n
>   q   = ?lula

> {-

> multQ : NonNegQ -> NonNegQ -> NonNegQ
> multQ (MkNonNegQ m1 n1 p1) (MkNonNegQ m2 n2 p2) = MkNonNegQ m n p where



|SimpleProb| is a functor:

> fmap : {A, B : Type} -> (A -> B) -> SimpleProb A -> SimpleProb B
> fmap f (MkSimpleProb as ps p q) = MkSimpleProb (map f as) ps p q


|SimpleProb| is a monad:

> ret : {A : Type} -> A -> SimpleProb A
> ret {A} a = MkSimpleProb as ps p q where
>   n  : Nat
>   n  = S Z
>   as : Vect n A
>   as = a   :: Nil
>   ps : Vect n Float
>   ps = 1.0 :: Nil
>   p  : (k : Fin n) -> So (index k ps >= 0.0)
>   p  FZ    = Oh
>   p (FS k) = absurd k
>   q  : sum ps = 1.0
>   q  = Refl


> bind : {A, B : Type} -> SimpleProb A -> (A -> SimpleProb B) -> SimpleProb B
> bind {A} {B} (MkSimpleProb as ps p q) f = MkSimpleProb bs ps' p' q' where
>   n  : Nat
>   n  = length as
>   bs : Vect n B


|SimpleProb| is a container monad:

> ||| Membership
> Elem : {A : Type} -> (a : A) -> (ma : Identity A) -> Type
> Elem a1 (Id a2) = a1 = a2


> ||| Tagging
> tagElem  :  {A : Type} -> (ma : Identity A) -> Identity (a : A ** a `Elem` ma)
> tagElem (Id a) = Id (a ** Refl)

> ---}
