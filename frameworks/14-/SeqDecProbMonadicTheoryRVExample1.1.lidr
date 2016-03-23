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

> import SeqDecProbMonadicTheoryRV
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

> SeqDecProbMonadicTheoryRV.M = List

> SeqDecProbMonadicTheoryRV.fmap = ListOperations.fmap

> SeqDecProbMonadicTheoryRV.ret = ListOperations.ret
> -- %freeze ret

> SeqDecProbMonadicTheoryRV.bind = ListOperations.bind
> -- %freeze bind


** M is a container monad:

> SeqDecProbMonadicTheoryRV.Elem = Data.List.Elem

> SeqDecProbMonadicTheoryRV.All = Data.List.Quantifiers.All

> SeqDecProbMonadicTheoryRV.tagElem = ListOperations.tagElem
> -- %freeze tagElem

> SeqDecProbMonadicTheoryRV.containerMonadSpec3 = ListProperties.containerMonadSpec3
> -- %freeze containerMonadSpec3


** M is measurable:

> SeqDecProbMonadicTheoryRV.meas = sum

> SeqDecProbMonadicTheoryRV.measMon = sumMon
> -- %freeze measMon


* The decision process:

> maxColumn : Nat
> maxColumn = 10
> -- %freeze maxColumn

> nColumns : Nat
> nColumns = S maxColumn


** States:

> SeqDecProbMonadicTheoryRV.X t = LTB nColumns

> column : {t : Nat} -> X t -> Nat
> column = outl
> -- %freeze column

> SeqDecProbMonadicTheoryRV.TabulatedBackwardsInduction.fX t = finiteLTB _
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

> SeqDecProbMonadicTheoryRV.Y t x = Action

*** Controls are finite:

> fY : (t : Nat) -> (x : X t) -> Finite (Y t x)
> fY t x = fAction
> -- %freeze fY

*** Controls are not empty:

> nefY : (t : Nat) -> (x : X t) -> NonEmpty (fY t x)
> nefY t x = nonEmptyLemma (fY t x) Left
> -- %freeze nefY


** Transition function:

> SeqDecProbMonadicTheoryRV.step t (MkSigma Z prf) Left =
>   [MkSigma maxColumn (ltIdS maxColumn)]
> SeqDecProbMonadicTheoryRV.step t (MkSigma (S n) prf) Left =
>   [MkSigma n (ltLemma1 n nColumns prf)]
> SeqDecProbMonadicTheoryRV.step t (MkSigma n prf) Ahead =
>   [MkSigma n prf]
> SeqDecProbMonadicTheoryRV.step t (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = [MkSigma (S n) (LTESucc p)]
>   | (No contra) = [MkSigma  Z    (LTESucc LTEZero)]
> -- %freeze step


** Reward function:

> SeqDecProbMonadicTheoryRV.reward t x y x' =
>   if column {t = S t} x' == Z
>   then (S Z)
>   else if S (column {t = S t} x') == nColumns
>        then (S (S Z))
>        else Z
> -- %freeze reward


* Viable and Reachable

> -- Viable : (n : Nat) -> X t -> Prop
> SeqDecProbMonadicTheoryRV.Viable _ _ = Unit

> -- viableSpec1 : (x : X t) -> Viable (S n) x -> Exists (\ y => All (Viable n) (step t x y))
> SeqDecProbMonadicTheoryRV.viableSpec1 {t} {n} x _ = s3 where
>   y : Y t x
>   y = Left
>   mx' : List (X (S t))
>   mx' = step t x y 
>   s2  : SeqDecProbMonadicTheoryRV.All (Viable {t = S t} n) mx'
>   s2  = all mx' where
>     all : (xs : List (X (S t))) -> SeqDecProbMonadicTheoryRV.All (Viable {t = S t} n) xs
>     all Nil = Nil
>     all (x :: xs) = () :: (all xs)
>   s3  : Exists {a = Y t x} (\ y => SeqDecProbMonadicTheoryRV.All (Viable {t = S t} n) (step t x y))
>   s3  = Evidence y s2
> -- %freeze viableSpec1

> -- Reachable : X t' -> Prop
> SeqDecProbMonadicTheoryRV.Reachable _ = Unit

> -- reachableSpec1 : (x : X t) -> Reachable {t' = t} x -> (y : Y t x) -> All (Reachable {t' = S t}) (step t x y)
> SeqDecProbMonadicTheoryRV.reachableSpec1 {t} x r y = all (step t x y) where
>   all : (xs : List (X (S t))) -> SeqDecProbMonadicTheoryRV.All (Reachable {t' = S t}) xs
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
>        Finite (Sigma (Y t x) (\ y => SeqDecProbMonadicTheoryRV.All (Viable {t = S t} n) (step t x y)))
> -- %freeze fYAV

non-emptiness is straightforward:

> neYAV : (t : Nat) -> (n : Nat) -> (x : X t) -> (v : Viable {t = t} (S n) x) ->
>         NonEmpty (fYAV t n x v)
> neYAV t n x v = 
>   nonEmptyLemma {A = Sigma (Y t x) (\ y => SeqDecProbMonadicTheoryRV.All (Viable {t = S t} n) (step t x y))}
>                 (fYAV t n x v) (MkSigma y av) where
>     yav : Exists {a = Y t x} (\ y => SeqDecProbMonadicTheoryRV.All (Viable {t = S t} n) (step t x y))
>     yav = viableSpec1 {t = t} {n = n} x v            
>     y   : Y t x
>     y   = getWitness yav
>     av  : SeqDecProbMonadicTheoryRV.All (Viable {t = S t} n) (step t x y)
>     av  = getProof yav
> -- %freeze neYAV

Thus, the problem is that of implementing |fYAV|. We already know that
|Y t x| is finite. If we manage to show that for every |y|, |All (Viable
n) (step t x y)| is also finite, we can apply |finiteSigmaLemma| from
|SigmaProperties| and we are done. We show the result in two steps

> fAll : {t : Nat} -> {P : X t -> Type} ->
>        Finite1 P -> (xs : List (X t)) -> Finite (SeqDecProbMonadicTheoryRV.All P xs)
> fAll = finiteAllLemma
> -- %freeze fAll

and

> mutual

>   fViable : (t : Nat) -> (n : Nat) -> (x : X t) -> Finite (Viable {t} n x)
>   fViable t  n    x  = finiteSingleton
>   -- %freeze fViable

>   f1AllViable : (t : Nat) -> (n : Nat) -> (x : X t) ->
>                 Finite1 (\ y => SeqDecProbMonadicTheoryRV.All (Viable {t = S t} n) (step t x y))
>   f1AllViable t n x y = fAll {t = t} {P = (Viable {t = S t} n)} (fViable (S t) n) (step t x y)
>   -- %freeze f1AllViable


With |f1AllViable| we can finally implement |fYAV|

> fYAV t n x v = finiteSigmaLemma0 (fY t x) (f1AllViable t n x)
> -- %freeze fYAV

and |max|, |argmax|:

> SeqDecProbMonadicTheoryRV.max  {t} {n} x v =
>   Opt.max {A = Sigma (Y t x) (\ y => SeqDecProbMonadicTheoryRV.All (Viable {t = S t} n) (step t x y))} 
>           {B = Nat} 
>           totalPreorderNatLTE 
>           (fYAV t n x v) 
>           (neYAV t n x v)

> SeqDecProbMonadicTheoryRV.argmax  {t} {n} x v  =
>   Opt.argmax {A = Sigma (Y t x) (\ y => SeqDecProbMonadicTheoryRV.All (Viable {t = S t} n) (step t x y))} 
>              {B = Nat}
>              totalPreorderNatLTE 
>              (fYAV t n x v) 
>              (neYAV t n x v)

> SeqDecProbMonadicTheoryRV.maxSpec {n} t x v =
>   Opt.maxSpec {A = Sigma (Y t x) (\ y => SeqDecProbMonadicTheoryRV.All (Viable {t = S t} n) (step t x y))} 
>               {B = Nat}
>               totalPreorderNatLTE 
>               (fYAV t n x v) 
>               (neYAV t n x v)
> -- %freeze maxSpec

> SeqDecProbMonadicTheoryRV.argmaxSpec {n} t x v =
>   Opt.argmaxSpec {A = Sigma (Y t x) (\ y => SeqDecProbMonadicTheoryRV.All (Viable {t = S t} n) (step t x y))} 
>                  {B = Nat}
>                  totalPreorderNatLTE 
>                  (fYAV t n x v) 
>                  (neYAV t n x v)
> -- %freeze argmaxSpec


* Decidability of Viable and Reachable

> dElem : {t : Nat} -> (x : X t) -> (mx : M (X t)) -> Dec (x `SeqDecProbMonadicTheoryRV.Elem` mx)
> dElem x mx = Data.List.isElem x mx
> -- %freeze dElem

> -- dReachable : {t' : Nat} -> (x' : X t') -> Dec (Reachable x')
> SeqDecProbMonadicTheoryRV.TabulatedBackwardsInduction.dReachable {t'} x' = Yes ()
> -- %freeze dReachable

> dAll : {t : Nat} -> (P : X t -> Prop) -> Dec1 P -> (mx : M (X t)) -> Dec (SeqDecProbMonadicTheoryRV.All P mx)
> dAll P dP mx = all dP mx
> -- %freeze dAll

> -- dViable : {t : Nat} -> (n : Nat) -> (x : X t) -> Dec (Viable n x)
> SeqDecProbMonadicTheoryRV.TabulatedBackwardsInduction.dViable {t} n x = Yes ()
> -- %freeze dViable


* The computation:

> showState : {t : Nat} -> X t -> String
> showState {t} x = show (column {t} x)
> -- %freeze showState

> showControl : {t : Nat} -> {x : X t} -> Y t x -> String
> showControl = show
> -- %freeze showControl

> showStateControl : {t : Nat} -> Sigma (X t) (Y t) -> String
> showStateControl {t} (MkSigma x y) = "(" ++ showState {t} x ++ " ** " ++ showControl {t} {x} y ++ ")"
> -- %freeze showStateControl

> showSCS : {t : Nat} -> {n : Nat} -> StateCtrlSeq t n -> String
> showSCS scs = "[" ++ show' "" scs ++ "]" where
>   show' : {t' : Nat} -> {n' : Nat} -> String -> StateCtrlSeq t' n' -> String
>   show' {t'} {n' =   Z}      acc (Nil x)      =
>     acc ++ "(" ++ showState {t = t'} x ++ " ** " ++ " " ++ ")" 
>   show' {t'} {n' = S m'} acc (p :: ps)    = 
>     show' {t' = S t'} {n' = m'} (acc ++ showStateControl p ++ ", ") ps
> -- %freeze showSCS

> showMSCS : {t : Nat} -> {n : Nat} -> List (StateCtrlSeq t n) -> String
> showMSCS scss = "[" ++ show' "" scss ++ "]" where
>   show' :  {t' : Nat} -> {n' : Nat} -> String -> List (StateCtrlSeq t' n') -> String
>   show' acc [] = acc
>   show' acc [scs] = acc ++ showSCS scs
>   show' acc (scs :: scss) = show' (acc ++ showSCS scs ++ ", ") scss
> -- %freeze showMSCS

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getLTB nColumns
>      case (dViable {t = Z} nSteps x0) of
>        (Yes v0) => do putStr ("computing optimal policies ...\n")
>                       ps   <- pure (bi Z nSteps)
>                       -- ps   <- pure (fst (biT Z nSteps))
>                       -- ps   <- pure (tabtrbi Z nSteps)
>                       putStr ("computing optimal controls ...\n")
>                       mxys <- pure (stateCtrlTrj x0 () v0 ps)
>                       putStrLn (showMSCS mxys)
>                       putStr ("done!\n")
>        (No _)   => putStr ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps\n")
> -- %freeze computation

> main : IO ()
> main = run computation
> -- %freeze main

> {-

> ---}


-- Local Variables:
-- idris-packages: ("effects")
-- End:
 
