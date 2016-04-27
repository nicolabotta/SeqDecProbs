> module Main

> import Decidable.Order

> import Data.Fin
> import Data.Vect
> import Data.List
> import Data.List.Quantifiers
> import Data.So
> import Control.Isomorphism
> import Effects
> import Effect.Exception
> import Effect.StdIO
> import Syntax.PreorderReasoning

> import SeqDecProbMonadicTheory
> import SeqDecProbMonadicUtils
> import ListOperations
> import ListProperties
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
> import UniqueProperties
> import SubType
> import Decidable
> import DecidableProperties
> import FiniteSubTypeProperties
> import Prop
> import EqualityProperties
> import SingletonProperties
> import Opt
> import TotalPreorder
> import EffectException
> import EffectStdIO
> import FinOperations
> import PairsOperations
> import Sigma

> %default total
> %auto_implicits off

> -- %logging 5

We reimplement the Example1 with |M = List|:


* The monad M (List):


** M is a monad:

> SeqDecProbMonadicTheory.M = List

> SeqDecProbMonadicTheory.fmap = ListOperations.fmap

> SeqDecProbMonadicTheory.ret = ListOperations.ret
> -- %freeze ret

> SeqDecProbMonadicTheory.bind = ListOperations.bind
> -- %freeze bind


** M is a container monad:

> SeqDecProbMonadicTheory.Elem = Data.List.Elem

> SeqDecProbMonadicTheory.All = Data.List.Quantifiers.All

> SeqDecProbMonadicTheory.tagElem = ListOperations.tagElem
> -- %freeze tagElem

> SeqDecProbMonadicTheory.containerMonadSpec3 = ListProperties.containerMonadSpec3
> -- %freeze containerMonadSpec3


** M is measurable:

> SeqDecProbMonadicTheory.meas = sum

> SeqDecProbMonadicTheory.measMon = sumMon
> -- %freeze measMon


* The decision process:

> maxColumn : Nat
> maxColumn = 10
> -- %freeze maxColumn

> nColumns : Nat
> nColumns = S maxColumn


** States:

> SeqDecProbMonadicTheory.X t = LTB nColumns

> column : {t : Nat} -> X t -> Nat
> column = outl
> -- %freeze column

> SeqDecProbMonadicTheory.TabulatedBackwardsInduction.fX t = finiteLTB _
> -- %freeze fX

** Actions:

> data Action = Left | Ahead | Right

> implementation Eq Action where
>   (==) Left   Left = True
>   (==) Left      _ = False
>   (==) Ahead Ahead = True
>   (==) Ahead     _ = False
>   (==) Right Right = True
>   (==) Right     _ = False

> implementation Show Action where
>   show Left  = "L"
>   show Ahead = "A"
>   show Right = "R"

*** Action is finite:

> to : Action -> Fin 3
> to Left  =        FZ
> to Ahead =     FS FZ
> to Right = FS (FS FZ)

> from : Fin 3 -> Action
> from             FZ   = Left
> from         (FS FZ)  = Ahead
> from     (FS (FS FZ)) = Right
> from (FS (FS (FS k))) = absurd k

> toFrom : (k : Fin 3) -> to (from k) = k
> toFrom             FZ   = Refl
> toFrom         (FS FZ)  = Refl
> toFrom     (FS (FS FZ)) = Refl
> toFrom (FS (FS (FS k))) = absurd k
> -- %freeze toFrom

> fromTo : (a : Action) -> from (to a) = a
> fromTo Left  = Refl
> fromTo Ahead = Refl
> fromTo Right = Refl
> -- %freeze fromTo

> fAction : Finite Action
> fAction = MkSigma 3 (MkIso to from toFrom fromTo)
> %freeze fAction

** Controls (admissible actions):

> SeqDecProbMonadicTheory.Y t x = Action

*** Controls are finite:

> fY : (t : Nat) -> (x : X t) -> Finite (Y t x)
> fY t x = fAction
> -- %freeze fY

*** Controls are not empty:

> nefY : (t : Nat) -> (x : X t) -> NonEmpty (fY t x)
> nefY t x = nonEmptyLemma (fY t x) Left
> -- %freeze nefY


** Transition function:

> SeqDecProbMonadicTheory.step t (MkSigma Z prf) Left =
>   [MkSigma maxColumn (ltIdS maxColumn)]
> SeqDecProbMonadicTheory.step t (MkSigma (S n) prf) Left =
>   [MkSigma n (ltLemma1 n nColumns prf)]
> SeqDecProbMonadicTheory.step t (MkSigma n prf) Ahead =
>   [MkSigma n prf]
> SeqDecProbMonadicTheory.step t (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = [MkSigma (S n) (LTESucc p)]
>   | (No contra) = [MkSigma  Z    (LTESucc LTEZero)]
> -- %freeze step


** Reward function:

> SeqDecProbMonadicTheory.reward t x y x' =
>   if column {t = S t} x' == Z
>   then (S Z)
>   else if S (column {t = S t} x') == nColumns
>        then (S (S Z))
>        else Z
> -- %freeze reward


* Viable and Reachable

> -- Viable : (n : Nat) -> X t -> Prop
> SeqDecProbMonadicTheory.Viable _ _ = Unit

> -- viableSpec1 : (x : X t) -> Viable (S n) x -> Exists (\ y => All (Viable n) (step t x y))
> SeqDecProbMonadicTheory.viableSpec1 {t} {n} x _ = s3 where
>   y : Y t x
>   y = Left
>   mx' : List (X (S t))
>   mx' = step t x y 
>   s2  : SeqDecProbMonadicTheory.All (Viable {t = S t} n) mx'
>   s2  = all mx' where
>     all : (xs : List (X (S t))) -> SeqDecProbMonadicTheory.All (Viable {t = S t} n) xs
>     all Nil = Nil
>     all (x :: xs) = () :: (all xs)
>   s3  : Exists {a = Y t x} (\ y => SeqDecProbMonadicTheory.All (Viable {t = S t} n) (step t x y))
>   s3  = Evidence y s2
> -- %freeze viableSpec1

> -- Reachable : X t' -> Prop
> SeqDecProbMonadicTheory.Reachable _ = Unit

> -- reachableSpec1 : (x : X t) -> Reachable {t' = t} x -> (y : Y t x) -> All (Reachable {t' = S t}) (step t x y)
> SeqDecProbMonadicTheory.reachableSpec1 {t} x r y = all (step t x y) where
>   all : (xs : List (X (S t))) -> SeqDecProbMonadicTheory.All (Reachable {t' = S t}) xs
>   all Nil = Nil
>   all (x :: xs) = () :: (all xs)

> -- %freeze reachableSpec1


* Max and argmax

We want to implement

< max    : {t : Nat} -> {n : Nat} -> 
<          (x : X t) -> 
<          .(Viable (S n) x) ->
<          (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Nat) ->
<          Nat
< argmax : {t : Nat} -> {n : Nat} -> 
<          (x : X t) -> 
<          .(Viable (S n) x) ->
<          (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Nat) ->
<          Sigma (Y t x) (\ y => All (Viable n) (step t x y))

This can be easily done using |Opt.max| and |Opt.argmax| if we can show
that |Sigma (Y t x) (\ y => All (Viable n) (step t x y))| is finite and
non-empty for every |t : Nat|, |x : X t| such that |Viable (S n) x|. If
we have finiteness

> fYAV : (t : Nat) -> (n : Nat) -> (x : X t) -> Viable {t = t} (S n) x ->
>        Finite (Sigma (Y t x) (\ y => SeqDecProbMonadicTheory.All (Viable {t = S t} n) (step t x y)))
> -- %freeze fYAV

non-emptiness is straightforward:

> neYAV : (t : Nat) -> (n : Nat) -> (x : X t) -> (v : Viable {t = t} (S n) x) ->
>         NonEmpty (fYAV t n x v)
> neYAV t n x v = 
>   nonEmptyLemma {A = Sigma (Y t x) (\ y => SeqDecProbMonadicTheory.All (Viable {t = S t} n) (step t x y))}
>                 (fYAV t n x v) (MkSigma y av) where
>     yav : Exists {a = Y t x} (\ y => SeqDecProbMonadicTheory.All (Viable {t = S t} n) (step t x y))
>     yav = viableSpec1 {t = t} {n = n} x v            
>     y   : Y t x
>     y   = getWitness yav
>     av  : SeqDecProbMonadicTheory.All (Viable {t = S t} n) (step t x y)
>     av  = getProof yav
> -- %freeze neYAV

Thus, the problem is that of implementing |fYAV|. We already know that
|Y t x| is finite. If we manage to show that for every |y|, |All (Viable
n) (step t x y)| is also finite, we can apply |finiteSigmaLemma| from
|SigmaProperties| and we are done. We show the result in two steps

> fAll : {t : Nat} -> {P : X t -> Type} ->
>        Finite1 P -> (xs : List (X t)) -> Finite (SeqDecProbMonadicTheory.All P xs)
> fAll = finiteAllLemma
> -- %freeze fAll

and

> mutual

>   fViable : (t : Nat) -> (n : Nat) -> (x : X t) -> Finite (Viable {t} n x)
>   fViable t  n    x  = finiteSingleton
>   -- %freeze fViable

>   f1AllViable : (t : Nat) -> (n : Nat) -> (x : X t) ->
>                 Finite1 (\ y => SeqDecProbMonadicTheory.All (Viable {t = S t} n) (step t x y))
>   f1AllViable t n x y = fAll {t = t} {P = (Viable {t = S t} n)} (fViable (S t) n) (step t x y)
>   -- %freeze f1AllViable


With |f1AllViable| we can finally implement |fYAV|

> fYAV t n x v = finiteSigmaLemma0 (fY t x) (f1AllViable t n x)
> -- %freeze fYAV

and |max|, |argmax|:

> SeqDecProbMonadicTheory.max  {t} {n} x v =
>   Opt.max {A = Sigma (Y t x) (\ y => SeqDecProbMonadicTheory.All (Viable {t = S t} n) (step t x y))} 
>           {B = Nat} 
>           totalPreorderNatLTE 
>           (fYAV t n x v) 
>           (neYAV t n x v)

> SeqDecProbMonadicTheory.argmax  {t} {n} x v  =
>   Opt.argmax {A = Sigma (Y t x) (\ y => SeqDecProbMonadicTheory.All (Viable {t = S t} n) (step t x y))} 
>              {B = Nat}
>              totalPreorderNatLTE 
>              (fYAV t n x v) 
>              (neYAV t n x v)

> SeqDecProbMonadicTheory.maxSpec {n} t x v =
>   Opt.maxSpec {A = Sigma (Y t x) (\ y => SeqDecProbMonadicTheory.All (Viable {t = S t} n) (step t x y))} 
>               {B = Nat}
>               totalPreorderNatLTE 
>               (fYAV t n x v) 
>               (neYAV t n x v)
> -- %freeze maxSpec

> SeqDecProbMonadicTheory.argmaxSpec {n} t x v =
>   Opt.argmaxSpec {A = Sigma (Y t x) (\ y => SeqDecProbMonadicTheory.All (Viable {t = S t} n) (step t x y))} 
>                  {B = Nat}
>                  totalPreorderNatLTE 
>                  (fYAV t n x v) 
>                  (neYAV t n x v)
> -- %freeze argmaxSpec


* Decidability of Viable and Reachable

> dElem : {t : Nat} -> (x : X t) -> (mx : M (X t)) -> Dec (x `SeqDecProbMonadicTheory.Elem` mx)
> dElem x mx = Data.List.isElem x mx
> -- %freeze dElem

> -- dReachable : {t' : Nat} -> (x' : X t') -> Dec (Reachable x')
> SeqDecProbMonadicTheory.TabulatedBackwardsInduction.dReachable {t'} x' = Yes ()
> -- %freeze dReachable

> dAll : {t : Nat} -> (P : X t -> Prop) -> Dec1 P -> (mx : M (X t)) -> Dec (SeqDecProbMonadicTheory.All P mx)
> dAll P dP mx = all dP mx
> -- %freeze dAll

> -- dViable : {t : Nat} -> (n : Nat) -> (x : X t) -> Dec (Viable n x)
> SeqDecProbMonadicTheory.TabulatedBackwardsInduction.dViable {t} n x = Yes ()
> -- %freeze dViable


* The computation:

> -- showState : {t : Nat} -> X t -> String
> SeqDecProbMonadicUtils.showState {t} x = show (column {t} x)
> -- %freeze showState

> -- showControl : {t : Nat} -> {x : X t} -> Y t x -> String
> SeqDecProbMonadicUtils.showCtrl = show
> -- %freeze showControl

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getLTB nColumns
>      case (dViable {t = Z} nSteps x0) of
>        (Yes v0) => do putStrLn ("computing optimal policies ...")
>                       -- ps   <- pure (bi Z nSteps)
>                       -- ps   <- pure (fst (biT Z nSteps))
>                       ps   <- pure (tabtrbi Z nSteps)
>                       putStrLn ("computing optimal controls ...")
>                       mxys <- pure (stateCtrlTrj x0 () v0 ps)
>                       putStrLn (show mxys)
>                       putStrLn ("done!")
>        (No _)   => putStrLn ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps")
> -- %freeze computation

> main : IO ()
> main = run computation
> -- %freeze main


> {-

> pnSteps : Nat
> pnSteps = Z

> nSteps : Nat
> nSteps = S pnSteps

> x0 : X Z
> x0 = MkSigma (S Z) (LTESucc (LTESucc LTEZero))

> r0 : Reachable {t' = Z} x0
> r0 = ()

> v0 : Viable {t = Z} nSteps x0
> v0 = ()

> ps : PolicySeq Z nSteps
> ps = bi Z nSteps

> policy : {t : Nat} -> {n : Nat} -> PolicySeq t n -> Policy t n 
> policy {n = Z}   Nil = ()
> policy {n = S m} (p :: _) = p

> yp0 : Sigma (Y Z x0) (\ y => SeqDecProbMonadicTheory.All (Viable {t = S Z} pnSteps) (step Z x0 y))
> yp0 = (policy ps) x0 r0 v0

> y0 : Y Z x0
> y0 = getWitness yp0

> s0 : String
> s0 = showCtrl {t = Z} {x = x0} y0

> main : IO ()
> main = do putStrLn (showState {t = Z} x0)
>           -- putStrLn (showCtrl {t = Z} {x = x0} y0)
>           putStrLn s0
>           putStrLn ("done!")

> ---}


-- Local Variables:
-- idris-packages: ("effects")
-- End:
 
