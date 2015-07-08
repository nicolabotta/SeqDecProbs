> module Main

> import Decidable.Order

> import Data.Fin
> import Data.Vect
> import Data.So
> import Control.Monad.Identity
> import Control.Isomorphism
> import Effects
> import Effect.Exception
> import Effect.StdIO
> import Syntax.PreorderReasoning

> import SeqDecProbMonadicTheoryRV
> import IdentityOperations
> import IdentityProperties
> import BoundedNat
> import BoundedNatOperations
> import BoundedNatProperties
> import SigmaOperations
> import SigmaProperties
> import SubsetOperations
> import SubsetProperties
> import NatProperties
> import Finite
> import FiniteOperations
> import FiniteProperties
> import Unique
> import UniqueProperties
> import SoProperties
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

> %default total

> -- %logging 5

We reimplement the example from "S1306_Example2" in the new theory. |M|
is the identity monad:



* The monad M (Identity):


** M is a monad:

> SeqDecProbMonadicTheoryRV.M = Identity

> SeqDecProbMonadicTheoryRV.fmap = map

> SeqDecProbMonadicTheoryRV.ret = return

> SeqDecProbMonadicTheoryRV.bind = (>>=)


** M is a container monad:

> SeqDecProbMonadicTheoryRV.Elem = IdentityOperations.Elem

> -- SeqDecProbMonadicTheoryRV.All P (Id a) = P a
> -- SeqDecProbMonadicTheoryRV.All P (Id a) = P (unwrap (Id a))
> SeqDecProbMonadicTheoryRV.All P = P . unwrap

> SeqDecProbMonadicTheoryRV.tagElem = IdentityOperations.tagElem

> SeqDecProbMonadicTheoryRV.containerMonadSpec3 {A} {P} a1 (Id a2) pa2 a1eqa2 =
>   replace (sym a1eqa2) pa2

> -- SeqDecProbMonadicTheoryRV.containerMonadSpec3 {ma = Id a} pa Refl = pa


** M is measurable:

> SeqDecProbMonadicTheoryRV.meas (Id x) = x

> SeqDecProbMonadicTheoryRV.measMon f g prf (Id x) = prf x


* The decision process:

> maxColumnO2 : Nat

> maxColumn : Nat
> maxColumn = maxColumnO2 + maxColumnO2

> nColumns : Nat
> nColumns = S maxColumn


** States:

> SeqDecProbMonadicTheoryRV.X t = LTB nColumns

> column : X t -> Nat
> column = outl

> data Pos = L | R

> pos : (t : Nat) -> X t -> Pos
> pos t x with (decLTE (column {t} x) maxColumnO2)
>   | (Yes _) = L
>   | (No  _) = R

> SeqDecProbMonadicTheoryRV.TabulatedBackwardsInduction.fX t = finiteLTB _


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

> existsAdmissible : (t : Nat) -> (x : X t) -> Sigma Action (Admissible t x)
> existsAdmissible t x with (admissibleLemma t x)
>   | (Left al)  = MkSigma Left al
>   | (Right ar) = MkSigma Right ar

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



*** Controls proper:

> SeqDecProbMonadicTheoryRV.Y t x = SubType Action (Admissible t x) (u1Admissible t x)

*** Controls are finite:

> fY : (t : Nat) -> (x : X t) -> Finite (Y t x)
> fY t x = finiteSubTypeLemma0 fAction (d1Admissible t x) (u1Admissible t x)

*** Controls are not empty:

> nefY : (t : Nat) -> (x : X t) -> NonEmpty (fY t x)
> nefY t x = nonEmptyLemma (fY t x) (existsAdmissible t x)



** Transition function:

> SeqDecProbMonadicTheoryRV.step t (Z   ** prf) (Left  ** aL) =
>   Id (maxColumn ** ltIdS maxColumn)
> SeqDecProbMonadicTheoryRV.step t (S n ** prf) (Left  ** aL) =
>   Id (n ** ltLemma1 n nColumns prf)
> SeqDecProbMonadicTheoryRV.step t (n   ** prf) (Ahead ** aA) =
>   Id (n ** prf)
> SeqDecProbMonadicTheoryRV.step t (n   ** prf) (Right ** aR) with (decLT n maxColumn)
>   | (Yes p)     = Id (S n ** LTESucc p)
>   | (No contra) = Id (Z   ** LTESucc LTEZero)



** Reward function:

> SeqDecProbMonadicTheoryRV.reward t x y x' =
>   if column {t = S t} x' == Z
>   then (S Z)
>   else if S (column {t = S t} x') == nColumns
>        then (S (S Z))
>        else Z



* Predecessor, Viable and Reachable

> Pred : {t : Nat} -> X t -> X (S t) -> Prop
> Pred {t} x x'  =  Exists (\ y => x' `SeqDecProbMonadicTheoryRV.Elem` step t x y)

> -- Viable : (n : Nat) -> X t -> Prop
> {-
> SeqDecProbMonadicTheoryRV.Viable {t}  Z    _  =  Unit
> SeqDecProbMonadicTheoryRV.Viable {t} (S m) x  =  Exists (\ y => All (Viable {t = S t} m) (step t x y))
> ---}
> --{-
> SeqDecProbMonadicTheoryRV.Viable {t}  n    _  =  Unit
> ---}

> -- viableSpec1 : (x : X t) -> Viable (S n) x -> Exists (\ y => All (Viable n) (step t x y))
> {-
> SeqDecProbMonadicTheoryRV.viableSpec1 {t} x v = v
> ---}
> --{-
> SeqDecProbMonadicTheoryRV.viableSpec1 {t} {n} x _ = s3 where
>   y : Y t x
>   y = existsAdmissible t x
>   mx' : M (X (S t))
>   mx' = step t x y 
>   x'  : X (S t)
>   x'  = unwrap mx'
>   s1  : Viable {t = S t} n x'
>   s1  = ()
>   s2  : All (Viable {t = S t} n) mx'
>   s2  = s1
>   s3  : Exists {a = Y t x} (\ y => All (Viable {t = S t} n) mx')
>   s3  = Evidence y s2
> ---}

> -- Reachable : X t' -> Prop
> {-
> SeqDecProbMonadicTheoryRV.Reachable {t' =   Z} _   =  Unit
> SeqDecProbMonadicTheoryRV.Reachable {t' = S t} x'  = 
>   Exists (\ x => (Reachable {t' = t} x, Pred {t = t} x x'))
> ---}
> --{-
> SeqDecProbMonadicTheoryRV.Reachable {t' = Z}   _  =  Unit
> SeqDecProbMonadicTheoryRV.Reachable {t' = S t} x' with (pos (S t) x')
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
> ---}

> -- reachableSpec1 : (x : X t) -> Reachable {t' = t} x -> (y : Y t x) -> All (Reachable {t' = S t}) (step t x y)
> {-
> SeqDecProbMonadicTheoryRV.reachableSpec1 {t} x r y = s2 where
>   mx' : M (X (S t))
>   mx' = step t x y 
>   x'  : X (S t)
>   x'  = unwrap mx'
>   s1  : x' `SeqDecProbMonadicTheoryRV.Elem` mx'
>   s1  = unwrapElemLemma mx'
>   s2  : Reachable {t' = S t} x'
>   s2  = Evidence x (r , (Evidence y s1))
> ---}
> --{-
> SeqDecProbMonadicTheoryRV.reachableSpec1 x r y = believe_me ()
> ---}


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
>        Finite (Subset (Y t x) (\ y => All (Viable {t = S t} n) (step t x y)))

non-emptiness is straightforward:

> neYAV : (t : Nat) -> (n : Nat) -> (x : X t) -> (v : Viable {t = t} (S n) x) ->
>         NonEmpty (fYAV t n x v)
> {- 
> neYAV t n x (Evidence y v) =
>   nonEmptyLemma {A = Subset (Y t x) (\ y => All (Viable {t = S t} n) (step t x y))}
>                 (fYAV t n x (Evidence y v))
>                 (Element y v)
> ---}
> --{-
> neYAV t n x v = 
>   nonEmptyLemma {A = Subset (Y t x) (\ y => All (Viable {t = S t} n) (step t x y))}
>                 (fYAV t n x v) (Element y av) where
>     yav : Exists {a = Y t x} (\ y => All (Viable {t = S t} n) (step t x y))
>     yav = viableSpec1 {t = t} {n = n} x v            
>     y   : Y t x
>     y   = getWitness yav
>     av  : All (Viable {t = S t} n) (step t x y)
>     av  = getProof yav
> ---}

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
>   {-
>   fViable t  Z    x  = finiteSingleton
>   fViable t (S m) x  = s3 where
>     s3 : Finite (Exists {a = Y t x} (\ y => All (Viable {t = S t} m) (step t x y)))
>     s3 = SubsetProperties.finiteExistsLemma (fY t x) (f1AllViable t m x)
>   ---}
>   --{
>   fViable t  n    x  = finiteSingleton
>   ---}

>   f1AllViable : (t : Nat) -> (n : Nat) -> (x : X t) ->
>                 Finite1 (\ y => All (Viable {t = S t} n) (step t x y))
>   f1AllViable t n x y = fAll {t = t} {P = (Viable {t = S t} n)} (fViable (S t) n) (step t x y)

With |f1AllViable| we can finally implement |fYAV|

> fYAV t n x v = finiteSubsetLemma0 (fY t x) (f1AllViable t n x)

and |max|, |argmax|:

> SeqDecProbMonadicTheoryRV.max  {t} {n} x v =
>   Opt.max {A = Subset (Y t x) (\ y => All (Viable {t = S t} n) (step t x y))} 
>           {B = Nat} 
>           totalPreorderNatLTE 
>           (fYAV t n x v) 
>           (neYAV t n x v)

> SeqDecProbMonadicTheoryRV.argmax  {t} {n} x v  =
>   Opt.argmax {A = Subset (Y t x) (\ y => All (Viable {t = S t} n) (step t x y))} 
>              {B = Nat}
>              totalPreorderNatLTE 
>              (fYAV t n x v) 
>              (neYAV t n x v)

-- > SeqDecProbMonadicTheoryRV.maxSpec {n} t x v =
-- >   Opt.maxSpec {A = Subset (Y t x) (\ y => All (Viable {t = S t} n) (step t x y))} 
-- >               {B = Nat}
-- >               totalPreorderNatLTE 
-- >               (fYAV t n x v) 
-- >               (neYAV t n x v)


* Decidability of Viable and Reachable

> dElem : {t : Nat} -> (x : X t) -> (mx : M (X t)) -> Dec (x `SeqDecProbMonadicTheoryRV.Elem` mx)
> dElem x (Id x') = decEqLTB x x'

> dPred : {t : Nat} -> (x : X t) -> (x' : X (S t)) -> Dec (Pred {t = t} x x')
> dPred {t} x x' = finiteDecLemma (fY t x) d1Elem where
>   d1Elem : Dec1 (\ y => x' `SeqDecProbMonadicTheoryRV.Elem` (step t x y))
>   d1Elem y = dElem {t = S t} x' (step t x y)

> -- dReachable : {t' : Nat} -> (x' : X t') -> Dec (Reachable x')
> {-
> SeqDecProbMonadicTheoryRV.TabulatedBackwardsInduction.dReachable {t' = Z}   x' = Yes ()
> SeqDecProbMonadicTheoryRV.TabulatedBackwardsInduction.dReachable {t' = S t} x' = s1 where
>   s1 : Dec (Exists (\ x => (Reachable x, Pred x x')))
>   s1 = finiteDecLemma (fX t) (\x => decPair (dReachable x) (dPred x x'))
> ---}
> --{-
> SeqDecProbMonadicTheoryRV.TabulatedBackwardsInduction.dReachable {t' = Z}   x' = Yes ()
> SeqDecProbMonadicTheoryRV.TabulatedBackwardsInduction.dReachable {t' = S t} x' with (pos (S t) x')
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
> ---}

> dAll : {t : Nat} -> (P : X t -> Prop) -> Dec1 P -> (mx : M (X t)) -> Dec (All P mx)
> dAll P dP (Id x) = dP x

> -- dViable : {t : Nat} -> (n : Nat) -> (x : X t) -> Dec (Viable n x)
> {-
> SeqDecProbMonadicTheoryRV.TabulatedBackwardsInduction.dViable {t}  Z    x = Yes ()
> SeqDecProbMonadicTheoryRV.TabulatedBackwardsInduction.dViable {t} (S m) x = s3 where
>     s1    :  Dec1 (\ y => All (Viable {t = S t} m) (step t x y))
>     s1 y  =  dAll {t = S t} (Viable {t = S t} m) (dViable {t = S t} m) (step t x y)
>     s2    :  Dec (Exists (\ y => All (Viable {t = S t} m) (step t x y)))
>     s2    =  finiteDecLemma (fY t x) s1
>     s3    :  Dec (Viable {t = t} (S m) x)
>     s3    =  s2
> ---}
> --{
> SeqDecProbMonadicTheoryRV.TabulatedBackwardsInduction.dViable {t}  n    x = Yes ()
> ---}



* The computation:

** Actions of state/control sequences

> actions : (t : Nat) ->
>           (n : Nat) ->
>           Identity (StateCtrlSeq t n) ->
>           Vect n Action
> actions _ Z _ = Nil
> actions t (S n) (Id ((x ** y) :: xys))
>   =
>   (outl y) :: (actions (S t) n (Id xys))

> showState : X t -> String
> showState {t} x = show (column {t} x)
> showControl : Y t x -> String
> showControl y = show (getWitness y)
>
> showStateControl : (x : X t ** Y t x) -> String
> showStateControl {t} (x ** y) = showState {t} x ++ " ** " ++ showControl y

> showSCS : StateCtrlSeq t n -> String
> showSCS {t} (Nil x)   = "Nil" ++ showState {t} x
> showSCS (p :: ps) = showStateControl p ++ " :: " ++ showSCS ps

> showMSCS : Identity (StateCtrlSeq t n) -> String
> showMSCS (Id scs) = showSCS scs

** Computation

> showSeq : PolicySeq t n -> String
> showSeq Nil = "Nil"
> showSeq (p :: ps) = "? :: " ++ showSeq ps


> %assert_total
> bie : (t : Nat) -> (n : Nat) -> ({ [STDIO] } Eff (PolicySeq t n))
> bie t  Z     =  pure Nil
> bie t (S n)  =  do ps <- bie (S t) n
>                    putStrLn (showSeq ps)
>                    pure (optExt ps :: ps)

> %assert_total
> firstControl : (t : Nat) -> (n : Nat) -> 
>                (x : X t) -> (r : Reachable {t' = t} x) -> (v : Viable {t = t} n x) -> 
>                PolicySeq t n -> { [STDIO] } Eff ()
> firstControl t  Z    x r v Nil       = putStr ("void policy sequence\n")
> firstControl t (S m) x r v (p :: ps) = do yav <- pure (p x r v)
>                                           a <- pure (getWitness (getWitness yav))
>                                           putStr ("first control: " ++ (show a) ++ "\n")

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getLTB nColumns
>      case (dViable {t = Z} nSteps x0) of
>        (Yes v0) => do putStr ("computing optimal policies ...\n")
>                       -- ps   <- pure (bi Z nSteps)
>                       -- ps   <- pure (fst (biT Z nSteps))
>                       ps   <- pure (tabtrbi Z nSteps)
>                       -- firstControl Z nSteps x0 () v0 ps
>                       putStr ("computing optimal controls ...\n")
>                       mxys <- pure (stateCtrlTrj x0 () v0 ps)
>                       as   <- pure (actions Z nSteps mxys)
>                       putStrLn (show as)
>                       -- putStrLn (showMSCS mxys)
>        (No _)   => putStr ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps\n")

> maxColumnO2 = 50

> main : IO ()
> main = run computation

> ---}

-- Local Variables:
-- idris-packages: ("effects")
-- End:
