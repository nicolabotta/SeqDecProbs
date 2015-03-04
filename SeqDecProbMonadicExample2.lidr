> module SeqDecProbMonadicExample2


> import Data.Fin
> import Data.Vect
> import Data.So
> import Control.Monad.Identity
> import Control.Isomorphism

> import SeqDecProbMonadic
> import IdentityOperations
> import IdentityProperties
> import BoundedNat
> import BoundedNatOperations
> import BoundedNatProperties
> import SigmaOperations
> import NatProperties
> import Finite
> import FiniteOperations
> import FiniteProperties
> import Unique
> import SoProperties
> import SubType
> import Decidable
> import FiniteSubTypeProperties
> import Prop


> %default total 


We reimplement the example from "S1306_Example2" in the new theory. |M|
is the identity monad:

> SeqDecProbMonadic.M = Identity

> SeqDecProbMonadic.fmap = map

> SeqDecProbMonadic.ret = return

> SeqDecProbMonadic.bind = (>>=)

> SeqDecProbMonadic.Elem = IdentityOperations.Elem

> SeqDecProbMonadic.tagElem = IdentityOperations.tagElem


The decision process:

> maxColumnO2 : Nat
> maxColumnO2 = 2

> maxColumn : Nat
> maxColumn = maxColumnO2 + maxColumnO2

> nColumns : Nat
> nColumns = S maxColumn


States

> SeqDecProbMonadic.X t = LTB nColumns

> column : X t -> Nat
> column = outl

> states : (t : Nat) -> Vect nColumns (X t)
> states t = toVect (\ i => i)


Actions

> data Action = Left | Ahead | Right

> instance Eq Action where
>   (==) Left   Left = True
>   (==) Left      _ = False
>   (==) Ahead Ahead = True
>   (==) Ahead     _ = False
>   (==) Right Right = True
>   (==) Right     _ = False

> instance Show Action where
>   show Left  = "L"
>   show Ahead = "A"
>   show Right = "R"

Action is finite

> to : Action -> Fin 3
> to Left  =        FZ
> to Ahead =     FS FZ
> to Right = FS (FS FZ)

> %assert_total
> from : Fin 3 -> Action
> from         FZ   = Left
> from     (FS FZ)  = Ahead
> from (FS (FS FZ)) = Right

> %assert_total
> toFrom : (k : Fin 3) -> to (from k) = k
> toFrom         FZ   = Refl
> toFrom     (FS FZ)  = Refl
> toFrom (FS (FS FZ)) = Refl

> fromTo : (a : Action) -> from (to a) = a
> fromTo Left  = Refl
> fromTo Ahead = Refl
> fromTo Right = Refl

> fAction : Finite Action
> fAction = Evidence 3 (MkIso to from toFrom fromTo)

> admissible : (t : Nat) -> X t -> Action -> Bool
> admissible t x Ahead = column {t} x == 0 || column {t} x == maxColumn
> admissible t x Left  = column {t} x <= maxColumnO2
> admissible t x Right = column {t} x >= maxColumnO2

> Admissible : (t : Nat) -> X t -> Action -> Type
> Admissible t x a = So (admissible t x a)

> d1Admissible : (t : Nat) -> (x : X t) -> Dec1 (Admissible t x)
> d1Admissible t x = dec1So {A = Action} (admissible t x) 

> u1Admissible : (t : Nat) -> (x : X t) -> Unique1 (Admissible t x)
> u1Admissible t x = unique1So {A = Action} (admissible t x) 


Controls

> SeqDecProbMonadic.Y t x = SubType Action (Admissible t x) (u1Admissible t x)

> action : Y t x -> Action
> action (a ** _) = a


Controls are finite

> fY : (t : Nat) -> (x : X t) -> Finite (Y t x)
> fY t x = finiteSubTypeLemma0 fAction (d1Admissible t x) (u1Admissible t x)


Controls are not empty

> %assert_total
> nefY : (t : Nat) -> (x : X t) -> NonEmpty (fY t x)
> nefY t (Z               ** prf) = nonEmptyLemma (fY t (Z               ** prf)) (Ahead ** Oh)
> nefY t (S Z             ** prf) = nonEmptyLemma (fY t (S Z             ** prf)) (Left  ** Oh)
> nefY t (S (S Z)         ** prf) = nonEmptyLemma (fY t (S (S Z)         ** prf)) (Left  ** Oh)
> nefY t (S (S (S Z))     ** prf) = nonEmptyLemma (fY t (S (S (S Z))     ** prf)) (Right ** Oh)
> nefY t (S (S (S (S Z))) ** prf) = nonEmptyLemma (fY t (S (S (S (S Z))) ** prf)) (Ahead ** Oh)

Transition function

> SeqDecProbMonadic.step t (Z   ** prf) (Left  ** aL) = 
>   Id (maxColumn ** ltIdS maxColumn)
> SeqDecProbMonadic.step t (S n ** prf) (Left  ** aL) = 
>   Id (n ** ltLemma1 n nColumns prf)
> SeqDecProbMonadic.step t (n   ** prf) (Ahead ** aA) = 
>   Id (n ** prf)
> SeqDecProbMonadic.step t (n   ** prf) (Right ** aR) with (decLT n maxColumn) 
>   | (Yes p)     = Id (S n ** LTESucc p)
>   | (No contra) = Id (Z   ** LTESucc LTEZero) 


Reward function

> SeqDecProbMonadic.reward t x y x' = 
>   if column {t = S t} x' == Z
>   then 1.0
>   else if S (column {t = S t} x') == nColumns
>        then 2.0
>        else 0.0


The measure

> SeqDecProbMonadic.meas (Id x) = x

> SeqDecProbMonadic.measMon f g prf (Id x) = prf x


Max and argmax

First, we derive decidability of equality on states

> decEqX : {t1, t2 : Nat} -> (x1 : X t1) -> (x2 : X t2) -> Dec (x1 = x2)
> decEqX x1 x2 = decEqLTB x1 x2 

and, from there, decidability of |Elem| and |All|

> decElem : {t : Nat} -> (x : X t) -> (mx : Identity (X t)) -> Dec (SeqDecProbMonadic.Elem x mx)
> decElem {t} = IdentityProperties.decElem (decEqX {t1 = t} {t2 = t})

> decAll : {t : Nat} -> (P : X t -> Prop) -> Dec1 P -> (mx : Identity (X t)) -> Dec (All P mx) 
> decAll {t} P dP (Id x) with (dP x)
>   | (Yes prf) = Yes prf' where
>     prf' : (x' : X t) -> x' `IdentityOperations.Elem` (Id x) -> P x'
>     prf' x' x'eqx = replace (sym x'eqx) prf
>   | (No contra) = No contra' where
>     contra' : (f : (x' : X t) -> x' `IdentityOperations.Elem` (Id x) -> P x') -> Void
>     contra' f = contra (f x Refl)

(it would be nice to implement |decAll| by applying a more general
|IdentityProperties.decAll| as done for |decElem|. At this point,
however, it is not clear how a |IdentityProperties.decAll| lemma could
be implemented. The problem is that |All| is defined in
|SeqDecProbMonadic| for every |M : Type -> Type|. Ideally, one would
like to collect the declatations of |Elem|, |tagElem| and the
declaration + definition of |All| in a |MonadicContainer| type class and
then show that |Identity| is an instance of |MonadicContainer|. A first
attempt to realize this design has led to issue #1975 (2015.03.03).

> decViable : (t : Nat) -> (n : Nat) -> (x : X t) -> Dec (Viable {t} n x)
> decViable t  Z    x = Yes ()
> decViable t (S m) x = s3 where
>   s1    :  Dec1 (\ y => All (Viable {t = S t} m) (step t x y))
>   s1 y  =  decAll {t = S t} (Viable {t = S t} m) (decViable (S t) m) (step t x y)
>   s2    :  Dec (Exists {a = Y t x} (\ y => All (Viable {t = S t} m) (step t x y)))
>   s2    =  finiteDecLemma (fY t x) s1
>   s3    :  Dec (Viable {t = t} (S m) x)
>   s3    =  s2


> {-

> max    : (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Float) -> 
>          Float

> ---}


