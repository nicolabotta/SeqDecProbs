> module Main


> import Vect.Ops
> import Util.VectExtensions1
> import Logic.Postulates
> import Logic.Properties
> import Float.Postulates
> import Float.Properties
> import Util.Opt
> import Util.Util
> import Exists.Ops

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability
> import DynamicProgramming.S1203_OptimalPolicies
> import DynamicProgramming.S1204_MaxArgmax
> import DynamicProgramming.S1205_BackwardsInduction

> %default total


We reimplement "S1206_Example1" by taking advantage of non-default
implemetations for |reachable| and |viable|. This improves run-time
efficiency by about 3 (7 seconds instead of 22 seconds for 6 steps).


# The context:

> maxColumnO2 : Nat
> maxColumnO2 = 2

> maxColumn : Nat
> maxColumn = maxColumnO2 + maxColumnO2

> nColumns : Nat
> nColumns = S maxColumn

> -- X : Nat -> Type
> Context.X t = Blt nColumns

> column : X t -> Nat
> column = outl

> states : (t : Nat) -> Vect nColumns (X t)
> states t = toVect (\ i => i)

> data Action = Left | Ahead | Right

> instance Show Action where
>   show Left = "L"
>   show Ahead = "A"
>   show Right = "R"

> admissible : X t -> Action -> Bool
> admissible {t = t} x Ahead = column {t} x == 0 || column {t} x == maxColumn
> admissible {t = t} x Left  = column {t} x <= maxColumnO2
> admissible {t = t} x Right = column {t} x >= maxColumnO2

> -- Y : (t : Nat) -> X t -> Type
> Context.Y t x = (a : Action ** so (admissible {t} x a))

> -- step : (t : Nat) -> (x : X t) -> Y t x -> X (S t)
> Context.step t (Z   ** q) (Left ** aL) = (maxColumn ** oh)
> Context.step t (S n ** q) (Left ** aL) = (n ** believe_me oh) -- trivial
> Context.step t (n ** q) (Ahead ** aA) = (n ** q)
> Context.step t (n ** q) (Right ** aR) = if n == maxColumn 
>                                         then (Z ** oh) 
>                                         else (S n ** believe_me oh)

> -- reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Float
> Context.reward t x y x' = if column {t = S t} x' == Z
>                           then 1.0
>                           else if S (column {t = S t} x') == nColumns
>                                then 2.0
>                                else 0.0

# Reachability, viability:

> -- ReachabilityViability.reachable : X t -> Bool
> ReachabilityViability.reachable {t} x =
>   if column {t} x == 0 || column {t} x == maxColumn then True
>      else abs (column {t} x - maxColumnO2) >= t                                                   

> -- ReachabilityViability.reachableSpec0 : 
> --   (x : X Z) -> 
> --   so (reachable x)
> ReachabilityViability.reachableSpec0 x = believe_me oh

> -- ReachabilityViability.reachableSpec1 : 
> --   (x : X t) ->
> --   so (reachable x) ->
> --   (y : Y t x) ->
> --   so (reachable {t = S t} (step t x y))
> ReachabilityViability.reachableSpec1 x r y = believe_me oh

> -- ReachabilityViability.reachableSpec2 : 
> --   (x : X (S t)) -> 
> --   so (reachable {t = S t} x) ->
> --   (x' : X t ** (y : Y t x' ** (so (reachable x'), x = step t x' y)))
> ReachabilityViability.reachableSpec2 {t} x rx = res where
>            i   : Nat
>            i   = column {t = S t} x
>            res : (x' : X t ** (y : Y t x' ** (so (reachable {t} x'), x = step t x' y)))
>            res = if i == 0 || i == maxColumn
>                     then  ((i ** believe_me oh) ** ((Ahead ** believe_me oh) ** 
>                                    (believe_me oh, believe_me oh)))
>                  else if i <= maxColumnO2 
>                         then ((S i ** believe_me oh) ** 
>                               ((Left ** believe_me oh) ** 
>                                (believe_me oh, believe_me oh)))
>                         else ((i - 1 ** believe_me oh) ** 
>                               ((Right ** believe_me oh) ** 
>                                (believe_me oh, believe_me oh)))

> -- ReachabilityViability.viable : (n : Nat) -> X t -> Bool
> ReachabilityViability.viable n x = True

> -- ReachabilityViability.viableSpec0 : 
> --   (x : X t) -> 
> --   so (viable Z x)
> ReachabilityViability.viableSpec0 x = oh

> -- ReachabilityViability.viableSpec1 : 
> --   (x : X t) -> 
> --   so (viable (S n) x) -> 
> --   (y : Y t x ** so (viable {t = S t} n (step t x y)))
> ReachabilityViability.viableSpec1 {t = t} x v = ((a ** believe_me oh) ** oh)
>   where
>     a : Action
>     a = if column {t} x <= maxColumnO2 then Left else Right

> -- ReachabilityViability.viableSpec2 : 
> --   (x : X t) -> 
> --   (y : Y t x ** so (viable {t = S t} n (step t x y))) ->
> --   so (viable (S n) x)
> ReachabilityViability.viableSpec2 x (y ** v) = oh


# Max, argmax

> eqeq : Action -> Action -> Bool
> eqeq Left  Left  = True
> eqeq Left  _     = False
> eqeq Ahead Ahead = True
> eqeq Ahead _     = False
> eqeq Right Right = True
> eqeq Right _     = False

> eqeqSpec1 : reflexive Action eqeq
> eqeqSpec1 = believe_me oh

> isIn : Action -> (n : Nat ** Vect n Action) -> Bool
> isIn = VectExtensions1.isIn Action eqeq eqeqSpec1

> lemma3 : (a : Action) ->
>          (p : Action -> Bool) ->
>          (as : (n : Nat ** Vect n Action)) ->
>          so (p a) ->
>          so (a `isIn` as) ->
>          so (isAnyBy p as)
> lemma3 = VectExtensions1.lemma3 Action eqeq eqeqSpec1

> admissiblesP : (x : X t) -> 
>                (v : so (viable {t} (S n) x)) -> 
>                (k : Nat ** Vect (S k) (Y t x))
> admissiblesP {t = t} {n = n} x v = filterTagP (admissible x) (outr s1) s6 where
>   s1 : (n : Nat ** Vect n Action)
>   s1 = (_ ** [Left, Right, Ahead])
>   s2 : (y : Y t x ** so (viable {t = S t} n (step t x y)))
>   s2 = viableSpec1 {t} {n} x v
>   s3 : Action
>   s3 = outl (outl s2)
>   s4 : so (s3 `isIn` s1)
>   s4 = believe_me oh
>   -- |Action| should be in |Enum| and |s1| should be set to |[toEnum 0
>   -- ..]|. Then |s4| would follow from a lemma of the kind:
>   -- (Enum alpha) => (a : alpha) -> so (a `isIn` toVect [toEnum 0 ..])
>   s5 : so (admissible {t} x s3)
>   s5 = outr (outl s2)
>   s6 : so (isAnyBy (admissible {t} x) s1)
>   s6 = lemma3 s3 (admissible {t} x) s1 s5 s4 

> yfysP : (n : Nat) ->
>         (x : X t) -> 
>         (v : so (viable {t} (S n) x)) ->
>         (f : (y : Y t x ** so (viable {t = S t} n (step t x y)))-> Float) -> 
>         (k : Nat 
>          ** 
>          Vect (S k) ((y : Y t x ** so (viable {t = S t} n (step t x y))), Float)
>         )
> yfysP {t = t} n x v f = fmapP (pair (id,f)) s5 where
>   s1 : (k : Nat ** Vect (S k) (Y t x))
>   s1 = admissiblesP {t} {n} x v
>   s2 : (k : Nat ** Vect k (Y t x))
>   s2 = (_ ** outr s1)
>   s3 : Y t x -> Bool
>   s3 y = viable {t = S t} n (step t x y)
>   s4 : so (isAnyBy s3 s2)
>   s4 = believe_me oh -- this should be more or less trivial
>   s5 : (k : Nat ** Vect (S k) (y : Y t x ** so (s3 y)))
>   s5 = filterTagP s3 (outr s2) s4

> MaxArgmax.max n x r v f = snd (maxP (outr (yfysP n x v f)))

> MaxArgmax.argmax n x r v f = fst (maxP (outr (yfysP n x v f)))

> MaxArgmax.maxSpec n x r v f yv = believe_me oh -- this should be
>                                                -- granted by |maxP|

> MaxArgmax.argmaxSpec n x r v f = believe_me oh -- this should be
>                                                -- granted by |maxP|

# The computation:

> nSteps : Nat
> nSteps = 8

> ps : PolicySeq Z nSteps
> ps = backwardsInduction Z nSteps

> controls : (t : Nat) -> 
>            (n : Nat) -> 
>            (x : X t) -> 
>            (r : so (reachable {t} x)) -> 
>            (v : so (viable {t} n x)) ->
>            PolicySeq t n -> 
>            Vect n Action
> controls _ Z _ _ _ _ = Nil
> controls t (S n) x r v (p :: ps) =
>   ((outl y) :: (controls (S t) n x' r' v' ps)) where
>     yq : (a : Y t x ** so (viable {t = S t} n (step t x a)))
>     yq = p x r v
>     y : Y t x    
>     y = outl yq
>     x' : X (S t)
>     x' = step t x y
>     r' : so (reachable {t = S t} x')
>     r' = reachableSpec1 x r y
>     v' : so (viable {t = S t} n x')
>     v' = outr yq

> x0 : X Z
> x0 = (2 ** oh)

> r0 : so (reachable {t = Z} x0)
> r0 = oh

> v0 : so (viable {t = Z} nSteps x0)
> v0 = oh

> as : Vect nSteps Action
> as = controls Z nSteps x0 r0 v0 ps

> main : IO ()
> main = putStrLn (show as)

