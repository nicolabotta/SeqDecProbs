> module Main


> import Data.Fin
> import Data.Vect
> import Data.So
> import Control.Monad.Identity
> import Control.Isomorphism
> import Effects
> import Effect.Exception
> import Effect.StdIO

> import SeqDecProbMonadicSmallTheory
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
> import TotalPreorder
> import EffectException
> import EffectStdIO
> import FinOperations


> %default total 


We reimplement the example from "S1306_Example2" in the new theory. |M|
is the identity monad:



* The monad M (Identity):


** M is a monad:

> SeqDecProbMonadicSmallTheory.M = Identity

> SeqDecProbMonadicSmallTheory.fmap = map

> SeqDecProbMonadicSmallTheory.ret = return

> SeqDecProbMonadicSmallTheory.bind = (>>=)


** M is a container monad:

> SeqDecProbMonadicSmallTheory.Elem = IdentityOperations.Elem

> SeqDecProbMonadicSmallTheory.All P (Id a) = P a

> SeqDecProbMonadicSmallTheory.tagElem = IdentityOperations.tagElem

> SeqDecProbMonadicSmallTheory.containerMonadSpec3 {A} {P} a1 (Id a2) pa2 a1eqa2 = 
>   replace (sym a1eqa2) pa2

> -- SeqDecProbMonadicSmallTheory.containerMonadSpec3 {ma = Id a} pa Refl = pa


** M is measurable:

> SeqDecProbMonadicSmallTheory.meas (Id x) = x



* The decision process:

> maxColumnO2 : Nat
> maxColumnO2 = 2

> maxColumn : Nat
> maxColumn = maxColumnO2 + maxColumnO2

> nColumns : Nat
> nColumns = S maxColumn


** States:

> SeqDecProbMonadicSmallTheory.X t = LTB nColumns

> column : X t -> Nat
> column = outl


** Actions:

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

*** Action is finite:

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


** Controls (admissible actions):

*** Admissibility:

> admissible : (t : Nat) -> X t -> Action -> Bool
> admissible t x Ahead = column {t} x == Z || column {t} x == maxColumn
> admissible t x Left  = column {t} x <= maxColumnO2
> admissible t x Right = column {t} x >= maxColumnO2

> Admissible : (t : Nat) -> X t -> Action -> Type
> Admissible t x a = So (admissible t x a)

If starting in the middle (with x = maxColumnO2) there is a genuine
choice between Left and Right. For Z < x < maxColumnO2 only Left is
allowed and for maxColumnO2 < x < maxColumn only Right. Finally in the
two "extreme" cases it is admitted to move Ahead or wrap around to the
other end. The system will then after a possible first transient
(moving just Left or just Right) end up in one extreme case and can
then move freely between those two states (and only those two states)
for each step.

*** Admissible is decidable and unique:

> d1Admissible : (t : Nat) -> (x : X t) -> Dec1 (Admissible t x)
> d1Admissible t x = dec1So {A = Action} (admissible t x) 

> u1Admissible : (t : Nat) -> (x : X t) -> Unique1 (Admissible t x)
> u1Admissible t x = unique1So {A = Action} (admissible t x) 

*** Controls proper:

> SeqDecProbMonadicSmallTheory.Y t x = SubType Action (Admissible t x) (u1Admissible t x)

*** Controls are finite:

> fY : (t : Nat) -> (x : X t) -> Finite (Y t x)
> fY t x = finiteSubTypeLemma0 fAction (d1Admissible t x) (u1Admissible t x)

*** Controls are not empty:

> %assert_total
> nefY : (t : Nat) -> (x : X t) -> NonEmpty (fY t x)
> nefY t (Z               ** prf) = nonEmptyLemma (fY t (Z               ** prf)) (Ahead ** Oh)
> nefY t (S Z             ** prf) = nonEmptyLemma (fY t (S Z             ** prf)) (Left  ** Oh)
> nefY t (S (S Z)         ** prf) = nonEmptyLemma (fY t (S (S Z)         ** prf)) (Left  ** Oh)
> nefY t (S (S (S Z))     ** prf) = nonEmptyLemma (fY t (S (S (S Z))     ** prf)) (Right ** Oh)
> nefY t (S (S (S (S Z))) ** prf) = nonEmptyLemma (fY t (S (S (S (S Z))) ** prf)) (Ahead ** Oh)


** Transition function:

> SeqDecProbMonadicSmallTheory.step t (Z   ** prf) (Left  ** aL) = 
>   Id (maxColumn ** ltIdS maxColumn)
> SeqDecProbMonadicSmallTheory.step t (S n ** prf) (Left  ** aL) = 
>   Id (n ** ltLemma1 n nColumns prf)
> SeqDecProbMonadicSmallTheory.step t (n   ** prf) (Ahead ** aA) = 
>   Id (n ** prf)
> SeqDecProbMonadicSmallTheory.step t (n   ** prf) (Right ** aR) with (decLT n maxColumn) 
>   | (Yes p)     = Id (S n ** LTESucc p)
>   | (No contra) = Id (Z   ** LTESucc LTEZero) 



** Reward function:

> SeqDecProbMonadicSmallTheory.reward t x y x' = 
>   if column {t = S t} x' == Z
>   then (S Z)
>   else if S (column {t = S t} x') == nColumns
>        then (S (S Z))
>        else Z



* Max and argmax

We want to implement

< max    : (t : Nat) -> (x : X t) -> Viable (S n) x ->
<          (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Nat) -> 
<          Nat
< argmax : (t : Nat) -> (x : X t) -> Viable (S n) x ->
<          (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Nat) -> 
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
>   f1AllViable t n x y = fAll {t = t} {P = (Viable {t = S t} n)} (Main.fViable (S t) n) (step t x y)

With |f1AllViable| we can finally implement |fYAV|

> fYAV t n x v = finiteSigmaLemma0 (fY t x) (f1AllViable t n x)

and |max|, |argmax|:

> SeqDecProbMonadicSmallTheory.max     {n} t x v  =  
>   Opt.max totalPreorderNatLTE (fYAV t n x v) (neYAV t n x v)

> SeqDecProbMonadicSmallTheory.argmax  {n} t x v  =  
>   Opt.argmax totalPreorderNatLTE (fYAV t n x v) (neYAV t n x v)



* The computation:

** Viable is decidable:

> dAll : (t : Nat) -> (P : X t -> Prop) -> Dec1 P -> (mx : Identity (X t)) -> Dec (All P mx) 
> dAll t P dP (Id x) = dP x

> dViable : (t : Nat) -> (n : Nat) -> (x : X t) -> Dec (Viable {t} n x)
> dViable t  Z    x = Yes ()
> dViable t (S m) x = s3 where
>   s1    :  Dec1 (\ y => All (Viable {t = S t} m) (step t x y))
>   s1 y  =  dAll (S t) (Viable {t = S t} m) (dViable (S t) m) (step t x y)
>   s2    :  Dec (Exists {a = Y t x} (\ y => All (Viable {t = S t} m) (step t x y)))
>   s2    =  finiteDecLemma (fY t x) s1
>   s3    :  Dec (Viable {t = t} (S m) x)
>   s3    =  s2


** Actions of state/control sequences

> actions : (t : Nat) -> 
>           (n : Nat) -> 
>           Identity (StateCtrlSeq t n) ->
>           Vect n Action
> actions _ Z _ = Nil
> actions t (S n) (Id ((x ** y) :: xys)) 
>   = 
>   (outl y) :: (actions (S t) n (Id xys))


** Computation

> computation : { [STDIO] } Eff ()
> computation = 
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getLTB nColumns
>      case (dViable Z nSteps x0) of
>        (Yes v0) => do ps   <- pure (trbi Z nSteps)
>                       mxys <- pure (stateCtrlTrj x0 () v0 ps)
>                       as   <- pure (actions Z nSteps mxys)
>                       putStrLn (show as)
>        (No _)   => putStr ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps\n")


> main : IO ()
> main = run computation

> ---}

-- Local Variables:
-- idris-packages: ("effects")
-- End:
