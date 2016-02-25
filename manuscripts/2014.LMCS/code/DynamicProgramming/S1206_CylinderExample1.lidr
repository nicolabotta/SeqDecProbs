> module Main

> import Data.So                -- So
> import Data.Vect              -- Vect
> import Effects                -- { [  ] } effects syntax
> -- import Effect.Exception
> import Effect.StdIO           -- STDIO, Eff

> import BoundedNat.Blt         -- Blt
> -- import Vect.Ops
> import Util.VectExtensions1   -- isEmpty
> -- import Logic.Postulates
> -- import Logic.Properties
> -- import Double.Postulates
> -- import Double.Properties
> import Util.Opt               -- maxP
> import Util.Util              -- pair
> import Exists.Ops             -- outl
> -- import EffectException
> import EffectStdIO            -- getNat

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability -- reachable
> import DynamicProgramming.S1203_OptimalPolicies       -- PolicySeq
> import DynamicProgramming.S1204_MaxArgmax             -- max
> import DynamicProgramming.S1205_BackwardsInduction    -- backwardsInduction
> import DynamicProgramming.S1202_ReachabilityViabilityDefaults -- eqeq

> %default total


We implement the case outlined in Fig. 6 of "S1200":

    6   | |r|r|r| |
    5   | |r|r|r| |
    4   | |r|r|r| |
    3   | |r|r|r| |
    2   | |r|r|r| |
    1   | | |r| | |
    0   | | | | | |

         0 1 2 3 4

# The context:

> maxColumnO2 : Nat
> maxColumnO2 = 2

> maxColumn : Nat
> maxColumn = maxColumnO2 + maxColumnO2

> nColumns : Nat
> nColumns = S maxColumn

> -- State : Nat -> Type
> Context.State t = Blt nColumns

> column : State t -> Nat
> column = outl

> states : (t : Nat) -> Vect Main.nColumns (State t)
> states t = toVect (\ i => i)

> data Action = Left | Ahead | Right

> Show Action where
>   show Left = "L"
>   show Ahead = "A"
>   show Right = "R"

> admissible : State t -> Action -> Bool
> admissible {t = t} x Ahead = column {t} x == Z || column {t} x == maxColumn
> admissible {t = t} x Left  = column {t} x <= maxColumnO2
> admissible {t = t} x Right = column {t} x >= maxColumnO2

> -- Ctrl : (t : Nat) -> State t -> Type
> Context.Ctrl t x = (a : Action ** So (admissible {t} x a))

> -- step : (t : Nat) -> (x : State t) -> Ctrl t x -> State (S t)
> Context.step t (Z   ** q) (Left ** aL) = (maxColumn ** Oh)
> Context.step t (S n ** q) (Left ** aL) = (n ** believe_me Oh) -- trivial
> Context.step t (n ** q) (Ahead ** aA) = (n ** q)
> Context.step t (n ** q) (Right ** aR) = if n == maxColumn
>                                         then (Z ** Oh)
>                                         else (S n ** believe_me Oh)

> -- reward : (t : Nat) -> (x : State t) -> Ctrl t x -> State (S t) -> Double
> Context.reward t x y x' = if column {t = S t} x' == Z
>                           then 1.0
>                           else if S (column {t = S t} x') == nColumns
>                                then 2.0
>                                else 0.0

# Reachability, viability:

> -- eqeq : State t -> State t -> Bool
> ReachabilityViabilityDefaults.eqeq {t = t} x x' =
>   column {t} x == column {t} x'

> -- eqeqSpec1 : (x : State t) -> So (eqeq x x)
> ReachabilityViabilityDefaults.eqeqSpec1 x = believe_me Oh

> pred : State t -> State (S t) -> Bool
> pred {t} x x' =
>   (admissible {t} x Left &&
>    eqeq {t = S t} x' (step t x (Left ** believe_me (admissible {t} x Left))))
>   ||
>   (admissible {t} x Ahead &&
>    eqeq {t = S t} x' (step t x (Ahead ** believe_me (admissible {t} x Ahead))))
>   ||
>   (admissible {t} x Right &&
>    eqeq {t = S t} x' (step t x (Right ** believe_me (admissible {t} x Right))))

> -- succs : State t -> (n : Nat ** Vect (State (S t)) n)
> ReachabilityViabilityDefaults.succs {t} x = filter (pred {t} x) (states (S t))

> -- preds : State (S t) -> (n : Nat ** Vect (State t) n)
> ReachabilityViabilityDefaults.preds {t} x' = filter (p t) (states t) where
>   p : (t : Nat) -> State t -> Bool
>   p t x = pred {t} x x'

> -- succsSpec1 : (x : State t) ->
> --              (y : Ctrl t x) ->
> --              So ((step t x y) `isIn` (succs x))
> ReachabilityViabilityDefaults.succsSpec1 x y = believe_me Oh -- ?

> -- succsSpec2 : (x : State t) ->
> --              (x' : State (S t)) ->
> --              So (x' `isIn` (succs x)) ->
> --              (y : Ctrl t x ** x' = step t x y)
> ReachabilityViabilityDefaults.succsSpec2 x x' x'inCsuccsx = believe_me Oh -- ?

> -- predsSpec1 : (x : State t) ->
> --              (y : Ctrl t x) ->
> --              So (x `isIn` (preds (step t x y)))
> ReachabilityViabilityDefaults.predsSpec1 x y = believe_me Oh -- ?

> -- predsSpec2 : (x' : State (S t)) ->
> --              (x : State t) ->
> --              So (x `isIn` (preds x')) ->
> --              (y : Ctrl t x ** x' = step t x y)
> ReachabilityViabilityDefaults.predsSpec2 x' x xinCpredsx' = believe_me Oh -- ?

> succsTh : (x : State t) -> So (not (isEmpty (succs {t} x)))
> succsTh x = believe_me Oh -- this should be more or less trivial

> viability : (n : Nat) -> (x : State t) -> So (viable {t} n x)
> viability {t}    Z x = viableSpec0 {t} x
> viability {t} (S n) k = step3 where
>   step0 : So (not (isEmpty (succs {t} k)))
>   step0 = succsTh k
>   step1 : (x' : State (S t) ** So (isIn {t = S t} x' (succs {t} k)))
>   step1 = lemma2 (succs k) step0
>   step2 : So (isAnyBy (viable {t = S t} n) (succs {t} k))
>   step2 = lemma3 x' (viable {t = S t} n) (succs k) vnx' x'inCsuccsx where
>     x' : State (S t)
>     x' = outl step1
>     vnx' : So (viable {t = S t} n x')
>     vnx' = viability {t = S t} n x' -- induction step
>     x'inCsuccsx : So (isIn {t = S t} x' (succs {t} k))
>     x'inCsuccsx = outr step1
>   step3 : So (viable {t} (S n) k)
>   step3 = believe_me step2

# Max, argmax

> eqeq : Action -> Action -> Bool
> eqeq Left  Left  = True
> eqeq Left  _     = False
> eqeq Ahead Ahead = True
> eqeq Ahead _     = False
> eqeq Right Right = True
> eqeq Right _     = False

> eqeqSpec1 : reflexive Action eqeq
> eqeqSpec1 = believe_me Oh

> isIn : Action -> (n : Nat ** Vect n Action) -> Bool
> isIn = VectExtensions1.isIn Action eqeq eqeqSpec1

> lemma3 : (a : Action) ->
>          (p : Action -> Bool) ->
>          (as : (n : Nat ** Vect n Action)) ->
>          So (p a) ->
>          So (a `isIn` as) ->
>          So (isAnyBy p as)
> lemma3 = VectExtensions1.lemma3 Action eqeq eqeqSpec1

> admissiblesP : (x : State t) ->
>                (v : So (viable {t} (S n) x)) ->
>                (k : Nat ** Vect (S k) (Ctrl t x))
> admissiblesP {t = t} {n = n} x v = filterTagP (admissible x) (outr s1) s6 where
>   s1 : (n : Nat ** Vect n Action)
>   s1 = (_ ** [Left, Right, Ahead])
>   s2 : (y : Ctrl t x ** So (viable {t = S t} n (step t x y)))
>   s2 = viableSpec1 {t} {n} x v
>   -- removing |{t}| and |{n}| from the definition of |s2| makes the
>   -- type checker eat-up the whole memory and stall
>   s3 : Action
>   s3 = outl (outl s2)
>   s4 : So (s3 `isIn` s1)
>   s4 = believe_me Oh
>   -- |Action| should be in |Enum| and |s1| should be set to |[toEnum 0
>   -- ..]|. Then |s4| would follow from a lemma of the kind:
>   -- (Enum alpha) => (a : alpha) -> So (a `isIn` toVect [toEnum 0 ..])
>   s5 : So (admissible {t} x s3)
>   s5 = outr (outl s2)
>   s6 : So (isAnyBy (admissible {t} x) s1)
>   s6 = lemma3 s3 (admissible x) s1 s5 s4

> yfysP : (n : Nat) ->
>         (x : State t) ->
>         (v : So (viable {t} (S n) x)) ->
>         (f : (y : Ctrl t x ** So (viable {t = S t} n (step t x y)))-> Double) ->
>         (k : Nat
>          **
>          Vect (S k) ((y : Ctrl t x ** So (viable {t = S t} n (step t x y))), Double)
>         )
> yfysP {t} n x v f = fmapP (pair (id,f)) s5 where
>   s1 : (k : Nat ** Vect (S k) (Ctrl t x))
>   s1 = admissiblesP x v
>   s2 : (k : Nat ** Vect k (Ctrl t x))
>   s2 = (_ ** outr s1)
>   s3 : Ctrl t x -> Bool
>   s3 y = viable {t = S t} n (step t x y)
>   s4 : So (isAnyBy s3 s2)
>   s4 = believe_me Oh -- this should be more or less trivial
>   s5 : (k : Nat ** Vect (S k) (y : Ctrl t x ** So (s3 y)))
>   s5 = filterTagP s3 (outr s2) s4

> MaxArgmax.max n x r v f = snd (maxP (outr (yfysP n x v f)))

> MaxArgmax.argmax n x r v f = fst (maxP (outr (yfysP n x v f)))

> MaxArgmax.maxSpec n x r v f yv = believe_me Oh -- this should be
>                                                -- granted by |maxP|

> MaxArgmax.argmaxSpec n x r v f = believe_me Oh -- this should be
>                                                -- granted by |maxP|


> controls : (t : Nat) ->
>            (n : Nat) ->
>            (x : State t) ->
>            (r : So (reachable {t} x)) -> -- DynamicProgramming.S1202_ReachabilityViability
>            (v : So (viable {t} n x)) ->
>            PolicySeq t n ->
>            Vect n Action
> controls _ Z _ _ _ _ = Nil
> controls t (S n) x r v (p :: ps) =
>   ((outl y) :: (controls (S t) n x' r' v' ps)) where
>     yq : (a : Ctrl t x ** So (viable {t = S t} n (step t x a)))
>     yq = p x r v
>     y : Ctrl t x
>     y = outl yq
>     x' : State (S t)
>     x' = step t x y
>     r' : So (reachable {t = S t} x')
>     r' = reachableSpec1 x r y
>     v' : So (viable {t = S t} n x')
>     v' = outr yq



# The computation:

> {-

> nSteps : Nat
> nSteps = 8

> ps : PolicySeq Z nSteps
> ps = backwardsInduction Z nSteps

> x0 : State Z
> x0 = (2 ** Oh)

> r0 : So (reachable {t = Z} x0)
> r0 = Oh

> v0 : So (viable {t = Z} nSteps x0)
> v0 = viability {t = Z} nSteps x0

> as : Vect nSteps Action
> as = controls Z nSteps x0 r0 v0 ps

> main : IO ()
> main = putStrLn (show as)

> -}


> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getBlt nColumns
>      r0 <- pure (reachable {t = Z} x0)
>      v0 <- pure (viable {t = Z} nSteps x0)
>      case (r0 && v0) of
>        True  => do ps <- pure (backwardsInduction Z nSteps)
>                    as <- pure (controls Z nSteps x0 (believe_me Oh) (believe_me Oh) ps)
>                    putStrLn (show as)
>        False => putStr ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps\n")

> main : IO ()
> main = run computation
