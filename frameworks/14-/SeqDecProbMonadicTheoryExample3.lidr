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

We reimplement the Example2 with |M = List|:


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

> maxColumnO2 : Nat
> maxColumnO2 = 5
> -- %freeze maxColumnO2

> maxColumn : Nat
> maxColumn = maxColumnO2 + maxColumnO2
> -- %freeze maxColumn

> nColumns : Nat
> nColumns = S maxColumn


** States:

> SeqDecProbMonadicTheory.X t = LTB nColumns

> column : {t : Nat} -> X t -> Nat
> column = outl
> -- %freeze column

> data Pos = L | R

> pos : (t : Nat) -> X t -> Pos
> pos t x with (decLTE (column {t} x) maxColumnO2)
>   | (Yes _) = L
>   | (No  _) = R
> -- %freeze pos

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

*** Admissibility:

> Admissible : (t : Nat) -> X t -> Action -> Type
> Admissible t x Ahead with (decEq (column {t} x) Z)
>   | (Yes _) = Unit
>   | (No  _) with (decEq (column {t} x) maxColumn)
>     | (Yes _) = Unit
>     | (No  _) = Void
> Admissible t x Left with (pos t x) 
>   | L = Unit
>   | R = Void
> Admissible t x Right with (pos t x) 
>   | L = Void
>   | R = Unit

> admissibleLemma : (t : Nat) -> (x : X t) -> Either (Admissible t x Left) (Admissible t x Right)
> admissibleLemma t x with (pos t x) 
>   | L = Left ()
>   | R = Right ()
> -- %freeze admissibleLemma

> existsAdmissible : (t : Nat) -> (x : X t) -> Sigma Action (Admissible t x)
> existsAdmissible t x with (admissibleLemma t x)
>   | (Left al)  = MkSigma Left al
>   | (Right ar) = MkSigma Right ar
> -- %freeze existsAdmissible

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
> d1Admissible t x Ahead with (decEq (column {t} x) Z)
>   | (Yes _) = Yes ()
>   | (No  _) with (decEq (column {t} x) maxColumn)
>     | (Yes _) = Yes ()
>     | (No  _) = No void 
> d1Admissible t x Left with (pos t x) 
>   | L = Yes ()
>   | R = No void
> d1Admissible t x Right with (pos t x) 
>   | L = No void
>   | R = Yes ()
> -- %freeze d1Admissible

> u1Admissible : (t : Nat) -> (x : X t) -> Unique1 (Admissible t x)
> u1Admissible t x Ahead p q with (decEq (column {t} x) Z)
>   u1Admissible t x Ahead () () | (Yes _) = Refl
>   u1Admissible t x Ahead p q   | (No  _) with (decEq (column {t} x) maxColumn)
>     u1Admissible t x Ahead () ()   | (No  _) | (Yes _) = Refl
>     u1Admissible t x Ahead p q     | (No  _) | (No  _) = void p
> u1Admissible t x Left p q with (pos t x) 
>   u1Admissible t x Left () () | L = Refl
>   u1Admissible t x Left p q   | R = void p
> u1Admissible t x Right p q with (pos t x) 
>   u1Admissible t x Right p q   | L = void p
>   u1Admissible t x Right () () | R = Refl
> -- %freeze u1Admissible


*** Controls proper:

> SeqDecProbMonadicTheory.Y t x = SubType Action (Admissible t x) (u1Admissible t x)

*** Controls are finite:

> fY : (t : Nat) -> (x : X t) -> Finite (Y t x)
> fY t x = finiteSubTypeLemma0 fAction (d1Admissible t x) (u1Admissible t x)
> -- %freeze fY

*** Controls are not empty:

> nefY : (t : Nat) -> (x : X t) -> NonEmpty (fY t x)
> nefY t x = nonEmptyLemma (fY t x) (existsAdmissible t x)
> -- %freeze nefY


** Transition function:

> SeqDecProbMonadicTheory.step t (MkSigma Z prf) (MkSigma Left aL) =
>   [MkSigma maxColumn (ltIdS maxColumn)]
> SeqDecProbMonadicTheory.step t (MkSigma (S n) prf) (MkSigma Left aL) =
>   [MkSigma n (ltLemma1 n nColumns prf)]
> SeqDecProbMonadicTheory.step t (MkSigma n prf) (MkSigma Ahead aA) =
>   [MkSigma n prf]
> SeqDecProbMonadicTheory.step t (MkSigma n prf) (MkSigma Right aR) with (decLT n maxColumn)
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


* Predecessor, Viable and Reachable

> Pred : {t : Nat} -> X t -> X (S t) -> Prop
> Pred {t} x x'  =  Exists (\ y => x' `SeqDecProbMonadicTheory.Elem` step t x y)

> -- Viable : (n : Nat) -> X t -> Prop
> SeqDecProbMonadicTheory.Viable {t}  n    _  =  Unit

> -- viableSpec1 : (x : X t) -> Viable (S n) x -> Exists (\ y => All (Viable n) (step t x y))
> SeqDecProbMonadicTheory.viableSpec1 {t} {n} x _ = s3 where
>   y : Y t x
>   y = existsAdmissible t x
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
> SeqDecProbMonadicTheory.Reachable {t' = Z}   _  =  Unit
> SeqDecProbMonadicTheory.Reachable {t' = S t} x' with (pos (S t) x')
>   | L with (decEq (column {t = (S t)} x') Z)
>     | Yes _ = Unit
>     | No  _ with (decLTE ((S t) + column {t = (S t)} x') maxColumnO2)
>       | Yes _ = Unit
>       | No  _ = Void
>   | R with (decEq (column {t = (S t)} x') maxColumn)
>     | Yes _ = Unit
>     | No  _ with (decLTE ((S t) + maxColumnO2) (column {t = (S t)} x'))
>       | Yes _ = Unit
>       | No  _ = Void

> -- reachableSpec1 : (x : X t) -> Reachable {t' = t} x -> (y : Y t x) -> All (Reachable {t' = S t}) (step t x y)
> SeqDecProbMonadicTheory.reachableSpec1 {t} (MkSigma Z prf) r (MkSigma Left aL) = () :: Nil
> -- SeqDecProbMonadicTheory.reachableSpec1 {t} (MkSigma (S n) prf) r (MkSigma Left aL) = () :: Nil
> -- %freeze reachableSpec1

SeqDecProbMonadicTheory.step t (MkSigma Z prf) (MkSigma Left aL) =
  [MkSigma maxColumn (ltIdS maxColumn)]
SeqDecProbMonadicTheory.step t (MkSigma (S n) prf) (MkSigma Left aL) =
  [MkSigma n (ltLemma1 n nColumns prf)]
SeqDecProbMonadicTheory.step t (MkSigma n prf) (MkSigma Ahead aA) =
  [MkSigma n prf]
SeqDecProbMonadicTheory.step t (MkSigma n prf) (MkSigma Right aR) with (decLT n maxColumn)
  | (Yes p)     = [MkSigma (S n) (LTESucc p)]
  | (No contra) = [MkSigma  Z    (LTESucc LTEZero)]


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

> dPred : {t : Nat} -> (x : X t) -> (x' : X (S t)) -> Dec (Pred {t = t} x x')
> dPred {t} x x' = finiteDecLemma (fY t x) d1Elem where
>   d1Elem : Dec1 (\ y => x' `SeqDecProbMonadicTheory.Elem` (step t x y))
>   d1Elem y = dElem {t = S t} x' (step t x y)
> -- %freeze dPred

> -- dReachable : {t' : Nat} -> (x' : X t') -> Dec (Reachable x')
> {-
> SeqDecProbMonadicTheory.TabulatedBackwardsInduction.dReachable {t' = Z}   x' = Yes ()
> SeqDecProbMonadicTheory.TabulatedBackwardsInduction.dReachable {t' = S t} x' = s1 where
>   s1 : Dec (Exists (\ x => (Reachable x, Pred x x')))
>   s1 = finiteDecLemma (fX t) (\x => decPair (dReachable x) (dPred x x'))
> ---}
> SeqDecProbMonadicTheory.TabulatedBackwardsInduction.dReachable {t' = Z}   x' = Yes ()
> SeqDecProbMonadicTheory.TabulatedBackwardsInduction.dReachable {t' = S t} x' with (pos (S t) x')
>   | L with (decEq (column {t = (S t)} x') Z)
>     | Yes _ = Yes ()
>     | No  _ with (decLTE ((S t) + column {t = (S t)} x') maxColumnO2)
>       | Yes _ = Yes ()
>       | No  _ = No void
>   | R with (decEq (column {t = (S t)} x') maxColumn)
>     | Yes _ = Yes ()
>     | No  _ with (decLTE ((S t) + maxColumnO2) (column {t = (S t)} x'))
>       | Yes _ = Yes ()
>       | No  _ = No void
> -- %freeze dReachable

> dAll : {t : Nat} -> (P : X t -> Prop) -> Dec1 P -> (mx : M (X t)) -> Dec (SeqDecProbMonadicTheory.All P mx)
> dAll P dP mx = all dP mx
> -- %freeze dAll

> -- dViable : {t : Nat} -> (n : Nat) -> (x : X t) -> Dec (Viable n x)
> {-
> SeqDecProbMonadicTheory.TabulatedBackwardsInduction.dViable {t}  Z    x = Yes ()
> SeqDecProbMonadicTheory.TabulatedBackwardsInduction.dViable {t} (S m) x = s3 where
>     s1    :  Dec1 (\ y => All (Viable {t = S t} m) (step t x y))
>     s1 y  =  dAll {t = S t} (Viable {t = S t} m) (dViable {t = S t} m) (step t x y)
>     s2    :  Dec (Exists (\ y => All (Viable {t = S t} m) (step t x y)))
>     s2    =  finiteDecLemma (fY t x) s1
>     s3    :  Dec (Viable {t = t} (S m) x)
>     s3    =  s2
> ---}
> SeqDecProbMonadicTheory.TabulatedBackwardsInduction.dViable {t}  n    x = Yes ()
> -- %freeze dViable


* The computation:

** Actions of state/control sequences

> lala : (t : Nat) ->
>        (n : Nat) ->
>        StateCtrlSeq t n ->
>        Vect n Action
> lala _ Z _ = Nil
> lala t (S n) ((MkSigma x y) :: xys) = (outl y) :: (lala (S t) n xys)
> -- %freeze lala

> actions : (t : Nat) ->
>           (n : Nat) ->
>           List (StateCtrlSeq t n) ->
>           List (Vect n Action)
> actions t n scss = map (lala t n) scss
> -- %freeze actions

> showState : {t : Nat} -> X t -> String
> showState {t} x = show (column {t} x)
> -- %freeze showState

> showControl : {t : Nat} -> {x : X t} -> Y t x -> String
> showControl y = show (getWitness y)
> -- %freeze showControl

> showStateControl : {t : Nat} -> Sigma (X t) (Y t) -> String
> showStateControl {t} (MkSigma x y) = "(" ++ showState {t} x ++ " ** " ++ showControl y ++ ")"
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


** Computation

> showSeq : {t : Nat} -> {n : Nat} -> PolicySeq t n -> String
> showSeq Nil = "Nil"
> showSeq (p :: ps) = "? :: " ++ showSeq ps
> -- %freeze showSeq

> %assert_total
> bie : (t : Nat) -> (n : Nat) -> ({ [STDIO] } Eff (PolicySeq t n))
> bie t  Z     =  pure Nil
> bie t (S n)  =  do ps <- bie (S t) n
>                    putStrLn (showSeq ps)
>                    pure (optExt ps :: ps)
> -- %freeze bie

> %assert_total
> firstControl : (t : Nat) -> (n : Nat) -> 
>                (x : X t) -> (r : Reachable {t' = t} x) -> (v : Viable {t = t} n x) -> 
>                PolicySeq t n -> { [STDIO] } Eff ()
> firstControl t  Z    x r v Nil       = putStr ("void policy sequence\n")
> firstControl t (S m) x r v (p :: ps) = do yav <- pure (p x r v)
>                                           a <- pure (getWitness (getWitness yav))
>                                           putStr ("first control: " ++ (show a) ++ "\n")
> -- %freeze firstControl

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
>                       -- firstControl Z nSteps x0 () v0 ps
>                       putStr ("computing optimal controls ...\n")
>                       mxys <- pure (stateCtrlTrj x0 () v0 ps)
>                       putStr ("done ...\n")
>                       -- as   <- pure (actions Z nSteps mxys)
>                       -- putStrLn (show as)
>                       -- putStrLn (showMSCS mxys)
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
 
