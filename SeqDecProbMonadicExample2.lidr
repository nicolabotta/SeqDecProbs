> module SeqDecProbMonadicExample2


> import Data.Fin
> import Data.Vect
> import Data.So
> import Control.Monad.Identity
> import Control.Isomorphism

> import SeqDecProbMonadic
> import BoundedNat
> import BoundedNatOperations
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


> %default total 


We reimplement the example from "S1306_Example2" in the new theory. |M|
is the identity monad:

> SeqDecProbMonadic.M = Identity

> SeqDecProbMonadic.fmap = map

> SeqDecProbMonadic.ret = return

> SeqDecProbMonadic.bind = (>>=)

> SeqDecProbMonadic.Elem a1 (Id a2) = a1 = a2

> SeqDecProbMonadic.tagElem (Id a) = Id (a ** Refl)


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





> {-

> ---}


