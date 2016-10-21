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

> import SeqDecProbsCoreAssumptions
> import SeqDecProbsCoreTheory
> import SeqDecProbsUtils
> import SeqDecProbsHelpers

> import SimpleProb
> import SimpleProbBasicOperations
> import SimpleProbBasicProperties
> import SimpleProbMonadicOperations
> import SimpleProbMonadicProperties
> import SimpleProbMeasures
> import BoundedNat
> import BoundedNatOperations
> import BoundedNatProperties
> import LeftAheadRight
> import Sigma
> import SigmaOperations
> import SigmaProperties
> import NatLTProperties
> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import NonNegRationalPredicates
> import NonNegRationalLTEProperties
> import Finite
> import FiniteOperations
> import FiniteProperties
> import Unique
> import Decidable
> import UnitProperties
> import Opt
> import TotalPreorder
> import EffectException
> import EffectStdIO
> import FinOperations
> import PairsOperations
> import Fraction
> import FractionNormal
> import PNat
> import NatPositive
> import ListOperations
> import FunOperations

> %default total
> %auto_implicits off


> -- %logging 5

Like "SeqDecProbsExample4.lidr", but selecting "Left" yields a non-zero
probablility to move "Ahead"!



* The monad M (SimpleProb):


** SimpleProb is a monad:

> SeqDecProbsCoreAssumptions.M = SimpleProb
> SeqDecProbsCoreAssumptions.fmap = SimpleProbMonadicOperations.fmap
> SeqDecProbsCoreAssumptions.ret = SimpleProbMonadicOperations.ret
> SeqDecProbsCoreAssumptions.bind = SimpleProbMonadicOperations.bind


** M is a container monad:

> SeqDecProbsCoreAssumptions.Elem = SimpleProbMonadicOperations.Elem
> SeqDecProbsCoreAssumptions.NonEmpty = SimpleProbMonadicOperations.NonEmpty
> SeqDecProbsCoreAssumptions.All = SimpleProbMonadicOperations.All
> SeqDecProbsCoreAssumptions.elemNonEmptySpec0 = SimpleProbMonadicProperties.elemNonEmptySpec0
> SeqDecProbsCoreAssumptions.elemNonEmptySpec1 = SimpleProbMonadicProperties.elemNonEmptySpec1
> SeqDecProbsCoreAssumptions.tagElem = SimpleProbMonadicOperations.tagElem
> SeqDecProbsCoreAssumptions.containerMonadSpec1 = SimpleProbMonadicProperties.containerMonadSpec1
> SeqDecProbsCoreAssumptions.containerMonadSpec3 = SimpleProbMonadicProperties.containerMonadSpec3



* The decision process:

> maxColumn : Nat
> maxColumn = 10
> %freeze maxColumn

> nColumns : Nat
> nColumns = S maxColumn


** States:

> SeqDecProbsCoreAssumptions.State t = LTB nColumns


** Controls:

> SeqDecProbsCoreAssumptions.Ctrl t x = LeftAheadRight


** Transition function:

> oo2  : NonNegRational
> oo2  = fromFraction (1, Element 2 MkPositive)

> SeqDecProbsCoreAssumptions.step t (MkSigma Z prf) Left =
>   SeqDecProbsCoreAssumptions.ret (MkSigma maxColumn (ltIdS maxColumn))
> SeqDecProbsCoreAssumptions.step t (MkSigma (S n) prf) Left =
>   MkSimpleProb [(MkSigma (S n) prf, oo2), 
>                 (MkSigma n (ltLemma1 n nColumns prf), oo2)] Refl

> SeqDecProbsCoreAssumptions.step t x Ahead = SeqDecProbsCoreAssumptions.ret x

> SeqDecProbsCoreAssumptions.step t (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = SeqDecProbsCoreAssumptions.ret (MkSigma (S n) (LTESucc p))
>   | (No contra) = SeqDecProbsCoreAssumptions.ret (MkSigma  Z    (LTESucc LTEZero))

> stepNonEmptyLemma : {t : Nat} -> 
>                     (x : State t) -> 
>                     SeqDecProbsCoreAssumptions.NonEmpty (step t x Ahead)
> stepNonEmptyLemma {t} x = SeqDecProbsCoreAssumptions.elemNonEmptySpec0 {A = State (S t)} x sp xesp where
>   sp : SimpleProb (State (S t))  
>   sp = step t x Ahead
>   xesp : SeqDecProbsCoreAssumptions.Elem x sp
>   xesp = SeqDecProbsCoreAssumptions.containerMonadSpec1


** Reward function:

> SeqDecProbsCoreAssumptions.Val = NonNegRational

> SeqDecProbsCoreAssumptions.reward t x y (MkSigma c _) =
>   if c == Z
>   then (fromInteger 1)
>   else if (S c) == nColumns
>        then (fromInteger 2)
>        else (fromInteger 0)

> SeqDecProbsCoreAssumptions.plus = NonNegRationalBasicOperations.plus
> SeqDecProbsCoreAssumptions.zero = fromInteger 0

> SeqDecProbsCoreAssumptions.LTE = NonNegRationalPredicates.LTE
> SeqDecProbsCoreAssumptions.reflexiveLTE = NonNegRationalLTEProperties.reflexiveLTE
> SeqDecProbsCoreAssumptions.transitiveLTE = NonNegRationalLTEProperties.transitiveLTE

> SeqDecProbsCoreAssumptions.monotonePlusLTE = NonNegRationalLTEProperties.monotonePlusLTE

** M is measurable:

> SeqDecProbsCoreAssumptions.meas = average
> SeqDecProbsCoreAssumptions.measMon = monotoneAverage



* Viable and Reachable

> -- Viable : (n : Nat) -> State t -> Type
> SeqDecProbsCoreAssumptions.Viable n x =  Unit

> viableLemma : {t : Nat} -> {n : Nat} ->
>               (x : State t) -> 
>               SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x Ahead)
> viableLemma (MkSigma n prf) = [()]

> -- viableSpec1 : (x : State t) -> Viable (S n) x -> GoodCtrl t x n
> SeqDecProbsCoreAssumptions.viableSpec1 {t} {n} x _ = MkSigma Ahead (ne, av) where
>   ne : SeqDecProbsCoreAssumptions.NonEmpty (step t x Ahead)
>   ne = stepNonEmptyLemma {t} x
>   av : SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x Ahead)
>   av = viableLemma x

> -- Reachable : State t' -> Type
> SeqDecProbsCoreAssumptions.Reachable x' = Unit

> -- reachableSpec1 : (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) -> All (Reachable {t' = S t}) (step t x y)
> SeqDecProbsCoreAssumptions.reachableSpec1 {t} x r y = all (step t x y) where
>   all : (sp : SimpleProb  (State (S t))) -> SeqDecProbsCoreAssumptions.All (Reachable {t' = S t}) sp
>   all sp = all' (support sp) where
>     all' : (xs : List (State (S t))) -> Data.List.Quantifiers.All (Reachable {t' = S t}) xs
>     all' Nil = Nil
>     all' (x :: xs) = () :: (all' xs)



* Max and argmax

We want to implement |max|, |argmax|, |maxSpec| and |argmaxSpec|. This
can be easily done in terms of |Opt.max| and |Opt.argmax| if we can show
that 

1) |LTE| is a *total* preorder 

2) |GoodCtrl t x n| is finite and, for every |t : Nat|, |x : State t|
   such that |Viable (S n) x|, its cardinality is not zero.

The first condition trivially holds 

> totalPreorderLTE : TotalPreorder Val
> totalPreorderLTE = MkTotalPreorder SeqDecProbsCoreAssumptions.LTE 
>                                    NonNegRationalLTEProperties.reflexiveLTE 
>                                    NonNegRationalLTEProperties.transitiveLTE 
>                                    NonNegRationalLTEProperties.totalLTE

Finiteness and non-zero cardinality of |GoodCtrl t x n|

< finiteGoodCtrl : {t : Nat} -> {n : Nat} -> 
<                  (x : State t) -> 
<                  Finite (GoodCtrl t x n) 

and

< cnzGoodCtrl : {t : Nat} -> {n : Nat} -> 
<               (x : State t) -> (v : Viable {t = t} (S n) x) ->
<               CardNotZ (finiteGoodCtrl {t} {n} x)

follow from finiteness of |All|

> -- finiteAll : {A : Type} -> {P : A -> Type} -> 
> --             Finite1 P -> (ma : M A) -> Finite (All P ma)
> SeqDecProbsHelpers.finiteAll = SimpleProbMonadicProperties.finiteAll

, finiteness of |Viable|

> -- finiteViable : {t : Nat} -> {n : Nat} -> 
> --                (x : State t) -> Finite (Viable {t} n x)
> SeqDecProbsHelpers.finiteViable _ = finiteUnit

, finiteness of |NonEmpty|

> -- finiteNonEmpty : {t : Nat} -> {n : Nat} -> 
> --                  (x : State t) -> (y : Ctrl t x) -> 
> --                  Finite (SeqDecProbsCoreAssumptions.NonEmpty (step t x y))
> SeqDecProbsHelpers.finiteNonEmpty {t} {n} x y = SimpleProbMonadicProperties.finiteNonEmpty (step t x y)

and, finally, finiteness of controls

> -- finiteCtrl : {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Ctrl t x) 
> SeqDecProbsHelpers.finiteCtrl _ = finiteLeftAheadRight
> %freeze SeqDecProbsHelpers.finiteCtrl

With these results in place, we have

> SeqDecProbsCoreAssumptions.max x v =
>   Opt.max totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v)

> SeqDecProbsCoreAssumptions.argmax x v  =
>   Opt.argmax totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v)

> SeqDecProbsCoreAssumptions.maxSpec x v =
>   Opt.maxSpec totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v)

> SeqDecProbsCoreAssumptions.argmaxSpec x v =
>   Opt.argmaxSpec totalPreorderLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v)



* Decidability of Viable

> dViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Dec (Viable {t} n x)
> dViable {t} n x = Yes ()



* The computation:

> -- showState : {t : Nat} -> State t -> String
> SeqDecProbsUtils.showState = show

> -- showControl : {t : Nat} -> {x : State t} -> Ctrl t x -> String
> SeqDecProbsUtils.showCtrl = show

> %freeze possibleStateCtrlSeqs
> %freeze possibleRewards'
> %freeze possibleStateCtrlSeqsRewards'
> %freeze meas
> %freeze support
> %freeze nonEmptyLemma
> %freeze totalPreorderLTE
> %freeze argmaxMax
> %freeze argminMin

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getLTB nColumns
>      case (dViable {t = Z} nSteps x0) of
>        (Yes v0) => do putStrLn ("computing optimal policies ...")
>                       ps   <- pure (bi Z nSteps)
>                       putStrLn ("computing optimal controls ...")
>                       mxys <- pure (possibleStateCtrlSeqs x0 () v0 ps)
>                       putStrLn "possible state-control sequences:"
>                       putStr "  "
>                       putStrLn (show mxys)
>                       mvs <- pure (possibleRewards' mxys)
>                       putStrLn "possible rewards:"
>                       putStr "  "
>                       putStrLn (show mvs)
>                       mxyvs <- pure (possibleStateCtrlSeqsRewards' mxys)
>                       putStrLn "possible state-control sequences and rewards:"
>                       putStr "  "
>                       putStrLn (show mxyvs)
>                       putStrLn "measure of possible rewards: "
>                       putStr "  "
>                       putStrLn (show (meas mvs))
>                       argmaxmax <- pure (argmaxMax {A = StateCtrlSeq Z nSteps} {B = Val} totalPreorderLTE (support mxyvs) (nonEmptyLemma mxyvs))
>                       putStrLn "best possible state-control sequence: "
>                       putStr "  "
>                       putStrLn (show (fst argmaxmax))
>                       -- putStrLn "best possible reward: "
>                       -- putStr "  "
>                       -- putStrLn (show (snd argmaxmax))
>                       -- -- argminmin <- pure (argminMin totalPreorderLTE (support mxyvs) (nonEmptyLemma mxyvs))
>                       -- -- putStrLn "worst possible state-control sequence: "
>                       -- -- putStr "  "
>                       -- -- putStrLn (show (fst argminmin))
>                       -- -- putStrLn "worst possible reward: "
>                       -- -- putStr "  "
>                       -- -- putStrLn (show (snd argminmin))
>                       putStrLn ("done!")                       
>        (No _)   => putStrLn ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps")

> main : IO ()
> main = run computation

> {-

> ---}

-- Local Variables:
-- idris-packages: ("effects")
-- End:
