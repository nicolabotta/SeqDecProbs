> module Main

> import Data.So
> import Data.Vect
> import Effects
> import Effect.Exception
> import Effect.StdIO

> import BoundedNat.Blt
> import Vect.Ops
> import Util.VectExtensions1
> import Logic.Postulates
> import Logic.Properties
> import Float.Postulates
> import Float.Properties
> import Util.Opt
> import Util.Util
> import Exists.Ops
> import EffectException
> import EffectStdIO

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability
> import DynamicProgramming.S1203_Controls
> import DynamicProgramming.S1203_OptimalPolicies
> import DynamicProgramming.S1204_MaxArgmax
> import DynamicProgramming.S1205_BackwardsInduction

> %default total


We reimplement "S1206_Example3" (a "cylinder" example similar to the one
illustrated in Figure 2 of the LMCS manuscript) by taking advantage of
non-default implementations for |reachable| and |viable|.


# The context:

> nColumns : Nat
> nColumns = 5

> valid : Nat -> Blt nColumns -> Bool
> -- valid t i = t /= 3 || outl i > 3
> valid t i with (decEq t 3)
>   | (Yes _) = outl i > 3
>   | (No  _) = True

> -- State : Nat -> Set
> Context.State t = (i : Blt nColumns ** So (valid t i))

> column : State t -> Nat
> column x = outl (outl x)

> (==) : State t -> State t -> Bool
> (==) x x' = column x == column x'

> states : (t : Nat) -> (n : Nat ** Vect n (State t))
> states t = zs where
>   xs : Vect nColumns (Blt nColumns)
>   xs = toVect (\ i => i)
>   ys : (n : Nat ** Vect n (Blt nColumns))
>   ys = filter (valid t) xs
>   zs : (n : Nat ** Vect n (State t))
>   zs = (_ ** map f (outr ys)) where
>     f : Blt nColumns -> State t
>     f i = (i ** believe_me (valid t i))

> data Action = Left | Ahead | Right

> instance Show Action where
>   show Left = "L"
>   show Ahead = "A"
>   show Right = "R"

> %assert_total
> admissible : State t -> Action -> Bool
> admissible {t} x Ahead =
>   valid (S t) (outl x)
> admissible {t} x Left with (Blt.toNat (outl x))
>   | Z    =  False
>   | S m  =  valid (S t) (decBlt (outl x))
> admissible {t} x Right =
>   S (column x) /= nColumns
>   &&
>   valid (S t) (incBlt (outl x) (believe_me Oh))

> -- Ctrl : (t : Nat) -> State t -> Type
> Context.Ctrl t x = (a : Action ** So (admissible x a))

> step' : Nat -> Action -> Nat
> step' (S i) Left  = i
> step' i     Ahead = i
> step' i     Right = S i
> --- dummy case, should never be called
> step' Z     Left  = Z

> step'Lemma : (x : State t) ->
>              (a : Action) ->
>              So (admissible x a) ->
>              So (step' (column x) a < nColumns)
> step'Lemma x a q = believe_me Oh

>
> -- step : (t : Nat) -> (x : State t) -> Ctrl t x -> State (S t)
> Context.step t x y = ((i' ** p') ** (believe_me Oh)) where
>   a : Action
>   a = outl y
>   i' : Nat
>   i' = step' (column x) a
>   p : So (admissible x a)
>   p = outr y
>   p' : So (i' < nColumns)
>   p' = step'Lemma x a p
>   -- q' : So (valid t (i' ** p'))
>   -- q' = ?step1

> -- reward : (t : Nat) -> (x : State t) -> Ctrl t x -> State (S t) -> Float
> Context.reward t x y x' = if column {t = S t} x' == Z
>                           then 2.0
>                           else if S (column {t = S t} x') == nColumns
>                                then 1.0
>                                else 0.0


# Reachability, viability:

> -- ReachabilityViability.reachable : State t -> Bool
> ReachabilityViability.reachable {t} x =
>   not (t > 3 && column x < 7 - t )

> -- ReachabilityViability.reachableSpec0 :
> --   (x : State Z) ->
> --   So (reachable x)
> ReachabilityViability.reachableSpec0 x = Oh

> -- ReachabilityViability.reachableSpec1 :
> --   (x : State t) ->
> --   So (reachable x) ->
> --   (y : Ctrl t x) ->
> --   So (reachable {t = S t} (step t x y))
> ReachabilityViability.reachableSpec1 {t} x r y = believe_me Oh

> -- ReachabilityViability.reachableSpec2 :
> --   (x : State (S t)) ->
> --   So (reachable {t = S t} x) ->
> --   (x' : State t ** (y : Ctrl t x' ** (So (reachable x'), x = step t x' y)))
> ReachabilityViability.reachableSpec2 {t} x rx = believe_me Oh

> -- ReachabilityViability.viable : (n : Nat) -> State t -> Bool
> ReachabilityViability.viable {t} n x =
>   (n == Z)
>   ||
>   (n == 1 && not (t == 2 && column x < 3))
>   ||
>   (n == 2 && not ((t == 2 && column x < 3)
>                   ||
>                   (t == 1 && column x < 2)))
>   ||
>   (n >= 3 && not ((t == 2 && column x < 3)
>                   ||
>                   (t == 1 && column x < 2)
>                   ||
>                   (t == 0 && column x < 1)))

> -- ReachabilityViability.viableSpec0 :
> --   (x : State t) ->
> --   So (viable Z x)
> ReachabilityViability.viableSpec0 x = Oh

> -- ReachabilityViability.viableSpec1 :
> --   (x : State t) ->
> --   So (viable (S n) x) ->
> --   (y : Ctrl t x ** So (viable {t = S t} n (step t x y)))
> ReachabilityViability.viableSpec1 {t} {n} x v = believe_me Oh

> -- ReachabilityViability.viableSpec2 :
> --   (x : State t) ->
> --   (y : Ctrl t x ** So (viable {t = S t} n (step t x y))) ->
> --   So (viable (S n) x)
> ReachabilityViability.viableSpec2 {t} {n} x (y ** v) = believe_me Oh


# Controls

> -- eqeq : Ctrl x t -> Ctrl x t -> Bool
> Controls.eqeq ( Left ** _) ( Left ** _) = True
> Controls.eqeq ( Left ** _) (    _ ** _) = False
> Controls.eqeq (Ahead ** _) (Ahead ** _) = True
> Controls.eqeq (Ahead ** _) (    _ ** _) = False
> Controls.eqeq (Right ** _) (Right ** _) = True
> Controls.eqeq (Right ** _) (    _ ** _) = False

> -- eqeqSpec1 : (y : Ctrl t x) -> So (eqeq y y)
> Controls.eqeqSpec1 ( Left ** _) = Oh
> Controls.eqeqSpec1 (Ahead ** _) = Oh
> Controls.eqeqSpec1 (Right ** _) = Oh


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
>                (v : So (viable (S n) x)) ->
>                (k : Nat ** Vect (S k) (Ctrl t x))
> admissiblesP {t = t} {n = n} x v = filterTagP (admissible x) (outr s1) s6 where
>   s1 : (n : Nat ** Vect n Action)
>   s1 = (_ ** [Left, Ahead, Right])
>   s2 : (y : Ctrl t x ** So (viable {t = S t} n (step t x y)))
>   s2 = viableSpec1 {t} {n} x v
>   s3 : Action
>   s3 = outl (outl s2)
>   postulate s4 : So (s3 `isIn` s1)
>   -- s4 = really_believe_me {b = So (s3 `isIn` s1)} Oh
>   -- |Action| should be in |Enum| and |s1| should be set to |[toEnum 0
>   -- ..]|. Then |s4| would follow from a lemma of the kind:
>   -- (Enum alpha) => (a : alpha) -> So (a `isIn` toVect [toEnum 0 ..])
>   s5 : So (admissible x s3)
>   s5 = outr (outl s2)
>   s6 : So (isAnyBy (admissible x) s1)
>   s6 = lemma3 s3 (admissible x) s1 s5 s4

> yfysP : (n : Nat) ->
>         (x : State t) ->
>         (v : So (viable (S n) x)) ->
>         (f : (y : Ctrl t x ** So (viable {t = S t} n (step t x y)))-> Float) ->
>         (k : Nat
>          **
>          Vect (S k) ((y : Ctrl t x ** So (viable {t = S t} n (step t x y))), Float)
>         )
> yfysP {t} n x v f = fmapP (pair (id,f)) s5 where
>   s1 : (k : Nat ** Vect (S k) (Ctrl t x))
>   s1 = admissiblesP x v
>   s2 : (k : Nat ** Vect k (Ctrl t x))
>   s2 = (_ ** outr s1)
>   s3 : Ctrl t x -> Bool
>   s3 y = viable {t = S t} n (step t x y)
>   %assert_total
>   s4 : So (isAnyBy s3 s2)
>   s4 = believe_me Oh -- this should be more or less trivial
>   s5 : (k : Nat ** Vect (S k) (y : Ctrl t x ** So (s3 y)))
>   s5 = filterTagP s3 (outr s1) s4

> MaxArgmax.max n x r v f = snd (maxP (outr (yfysP n x v f)))

> MaxArgmax.argmax n x r v f = fst (maxP (outr (yfysP n x v f)))

> MaxArgmax.maxSpec n x r v f yv =
>   really_believe_me {b = So (f yv <= max n x r v f)} Oh
>   -- this should be granted by |maxP|

> MaxArgmax.argmaxSpec n x r v f =
>   really_believe_me {b = So (f (argmax n x r v f) == max n x r v f)} Oh
>   -- this should be granted by |maxP|


> controls : (t : Nat) ->
>            (n : Nat) ->
>            (x : State t) ->
>            (r : So (reachable x)) ->
>            (v : So (viable n x)) ->
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

> nSteps : Nat
> nSteps = 4

> ps : PolicySeq Z nSteps
> ps = backwardsInduction Z nSteps

> x0 : State Z
> x0 = ((1 ** Oh) ** Oh)

> r0 : So (reachable {t = Z} x0)
> r0 = Oh

> v0 : So (viable {t = Z} nSteps x0)
> v0 = Oh

> as : Vect nSteps Action
> as = controls Z nSteps x0 r0 v0 ps

> main : IO ()
> main = putStrLn (show as)
