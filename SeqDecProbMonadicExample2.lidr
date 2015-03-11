> module Main


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
> import SigmaProperties
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
> import EqualityProperties
> import SingletonProperties
> import Opt
> import RelFloatProperties
> import Order


> %default total 


We reimplement the example from "S1306_Example2" in the new theory. |M|
is the identity monad:

> SeqDecProbMonadic.M = Identity

> SeqDecProbMonadic.fmap = map

> SeqDecProbMonadic.ret = return

> SeqDecProbMonadic.bind = (>>=)

> SeqDecProbMonadic.Elem = IdentityOperations.Elem

> SeqDecProbMonadic.All P (Id a) = P a

> SeqDecProbMonadic.tagElem = IdentityOperations.tagElem

> SeqDecProbMonadic.containerMonadSpec3 pa _ = ?lula -- pa


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

We want to implement

< max    : (t : Nat) -> (x : X t) -> Viable (S n) x ->
<          (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Float) -> 
<          Float
< argmax : (t : Nat) -> (x : X t) -> Viable (S n) x ->
<          (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Float) -> 
<          Sigma (Y t x) (\ y => All (Viable n) (step t x y))

This can be easily done using |Opt.max| and |Opt.argmax| if we can show
that |Sigma (Y t x) (\ y => All (Viable n) (step t x y))| is finite and
non-empty for every |t : Nat|, |x : X t| such that |Viable (S n) x|. If
we have finiteness

> fYAV : (t : Nat) -> (n : Nat) -> (x : X t) -> Viable (S n) x ->
>        Finite (Sigma (Y t x) (\ y => All (Viable {t = S t} n) (step t x y)))

non-emptiness is straightforward:

> neYAV : (t : Nat) -> (n : Nat) -> (x : X t) -> (v : Viable {t = t} (S n) x) ->
>         NonEmpty (fYAV t n x v)
> neYAV t n x (Evidence y v) = 
>   nonEmptyLemma {A = Sigma (Y t x) (\ y => All (Viable {t = S t} n) (step t x y))} 
>                 (fYAV t n x (Evidence y v)) 
>                 (y ** v)

Thus, the problem is that of implementing |fYAV|. We already know that
|Y t x| is finite. If we manage to show that for every |y|, |All (Viable
n) (step t x y)| is also finite, we can apply |finiteSigmaLemma| from
|SigmaProperties| and we are done. We show the result in two steps

> fAll : {t : Nat} -> {P : X t -> Type} -> 
>        Finite1 P -> (mx : Identity (X t)) -> Finite (All P mx)
> fAll f1P (Id x) = f1P x 

and 

> mutual

>   fViable : (t : Nat) -> (n : Nat) -> (x : X t) -> Finite (Viable {t} n x)
>   fViable t  Z    x  = finiteSingleton
>   fViable t (S m) x  = s3 where
>     s3 : Finite (Exists {a = Y t x} (\ y => All (Viable {t = S t} m) (step t x y)))
>     s3 = finiteExistsLemma (fY t x) (f1AllViable t m x)

>   f1AllViable : (t : Nat) -> (n : Nat) -> (x : X t) ->
>                 Finite1 (\ y => All (Viable {t = S t} n) (step t x y))
>   f1AllViable t n x y = fAll {t = t} {P = (Viable {t = S t} n)} (fViable (S t) n) (step t x y)

With |f1AllViable| we can finally implement |fYAV|

> fYAV t n x v = finiteSigmaLemma0 (fY t x) (f1AllViable t n x)

and |max|, |argmax|:

> SeqDecProbMonadic.max     {n} t x v  =  Opt.max     (fYAV t n  x v) (neYAV t n x v)

> SeqDecProbMonadic.argmax  {n} t x v  =  Opt.argmax  (fYAV t n  x v) (neYAV t n x v)

> -- SeqDecProbMonadic.maxSpec {n} t x v  =  Opt.maxSpec (fYAV t n  x v) (neYAV t n x v)

> -- SeqDecProbMonadic.argmaxSpec {n} t x v  =  Opt.argmaxSpec (fYAV t n  x v) (neYAV t n x v)


# The computation:

> nSteps : Nat
> nSteps = 8

> ps : PolicySeq Z nSteps
> ps = bi Z nSteps

> x0 : X Z
> x0 = (2 ** LTESucc (LTESucc (LTESucc LTEZero)))

> r0 : Reachable {t' = Z} x0
> r0 = ()

> postulate v0 : Viable {t = Z} nSteps x0

> mxys : Identity (StateCtrlSeq Z nSteps)
> mxys = stateCtrlTrj x0 r0 v0 ps

> actions : (t : Nat) -> 
>           (n : Nat) -> 
>           Identity (StateCtrlSeq t n) ->
>           Vect n Action
> actions _ Z _ = Nil
> actions t (S n) (Id ((x ** y) :: xys)) 
>   = 
>   (outl y) :: (actions (S t) n (Id xys))

> as : Vect nSteps Action
> as = actions Z nSteps mxys

> main : IO ()
> main = putStrLn (show as)

