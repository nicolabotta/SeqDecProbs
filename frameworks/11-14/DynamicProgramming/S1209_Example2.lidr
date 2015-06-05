> module Main

> import Data.So
> import Data.Vect

> import Vect.Ops
> import Util.VectExtensions1
> import Logic.Postulates
> import Logic.Properties
> import Float.Postulates
> import Float.Properties
> import Util.Opt
> import Util.Util
> import Exists.Ops

> import BoundedNat.Blt
> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability
> import DynamicProgramming.S1203_OptimalPolicies
> import DynamicProgramming.S1204_MaxArgmax
> import DynamicProgramming.S1205_BackwardsInduction
> import DynamicProgramming.S1207_FiniteState
> import DynamicProgramming.S1208_TabulatedBackwardsInduction

> %assert_total


We reimplement the example of |S1206_Example2.lidr| and compare the two
version of tabulated backwards induction implemented in
|S1208_TabulatedBackwardsInduction| to the standard algorithm.


# The context:

> maxColumnO2 : Nat
> maxColumnO2 = 2

> maxColumn : Nat
> maxColumn = maxColumnO2 + maxColumnO2

> nColumns : Nat
> nColumns = S maxColumn

> -- X : Type
> Context.X t = Blt nColumns

> column : X t -> Nat
> column = outl

> states : (t : Nat) -> Vect nColumns (X t)
> states t = toVect (\ i => i)

> data Action = Left | Ahead | Right

> instance Prelude.Show.Show Action where
>   show Left = "L"
>   show Ahead = "A"
>   show Right = "R"

> admissible : X t -> Action -> Bool
> admissible {t = t} x Ahead = column {t} x == 0 || column {t} x == maxColumn
> admissible {t = t} x Left  = column {t} x <= maxColumnO2
> admissible {t = t} x Right = column {t} x >= maxColumnO2

> -- Y : (t : Nat) -> X t -> Type
> Context.Y t x = (a : Action ** So (admissible {t} x a))

> -- step : (t : Nat) -> (x : X t) -> Y t x -> X (S t)
> Context.step t (Z   ** q) (Left ** aL) = (maxColumn ** Oh)
> Context.step t (S n ** q) (Left ** aL) = (n ** believe_me Oh) -- trivial
> -- Context.step t (n ** q) (Ahead ** aA) = (n ** q)
> -- user error (Internal error: "Codegen error:
> Context.step t (n ** q) (Ahead ** aA) = (n ** believe_me Oh)
> Context.step t (n ** q) (Right ** aR) = if n == maxColumn 
>                                         then (Z ** Oh) 
>                                         else (S n ** believe_me Oh)

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
> --   So (reachable x)
> ReachabilityViability.reachableSpec0 x = believe_me Oh

> -- ReachabilityViability.reachableSpec1 : 
> --   (x : X t) ->
> --   So (reachable x) ->
> --   (y : Y t x) ->
> --   So (reachable {t = S t} (step t x y))
> ReachabilityViability.reachableSpec1 x r y = believe_me Oh

> -- ReachabilityViability.reachableSpec2 : 
> --   (x : X (S t)) -> 
> --   So (reachable {t = S t} x) ->
> --   (x' : X t ** (y : Y t x' ** (So (reachable x'), x = step t x' y)))
> ReachabilityViability.reachableSpec2 {t} x rx = res where
>            i   : Nat
>            i   = column {t = S t} x
>            res : (x' : X t ** (y : Y t x' ** (So (reachable {t} x'), x = step t x' y)))
>            res = if i == 0 || i == maxColumn
>                     then  ((i ** believe_me Oh) ** ((Ahead ** believe_me Oh) ** 
>                                    (believe_me Oh, believe_me Oh)))
>                  else if i <= maxColumnO2 
>                         then ((S i ** believe_me Oh) ** 
>                               ((Left ** believe_me Oh) ** 
>                                (believe_me Oh, believe_me Oh)))
>                         else ((i - 1 ** believe_me Oh) ** 
>                               ((Right ** believe_me Oh) ** 
>                                (believe_me Oh, believe_me Oh)))

> -- ReachabilityViability.viable : (n : Nat) -> X t -> Bool
> ReachabilityViability.viable n x = True

> -- ReachabilityViability.viableSpec0 : 
> --   (x : X t) -> 
> --   So (viable O x)
> ReachabilityViability.viableSpec0 x = Oh

> -- ReachabilityViability.viableSpec1 : 
> --   (x : X t) -> 
> --   So (viable (S n) x) -> 
> --   (y : Y t x ** So (viable {t = S t} n (step t x y)))
> ReachabilityViability.viableSpec1 {t = t} x v = ((a ** believe_me Oh) ** Oh)
>   where
>     a : Action
>     a = if column {t} x <= maxColumnO2 then Left else Right

> -- ReachabilityViability.viableSpec2 : 
> --   (x : X t) -> 
> --   (y : Y t x ** So (viable {t = S t} n (step t x y))) ->
> --   So (viable (S n) x)
> ReachabilityViability.viableSpec2 x (y ** v) = Oh

> viability : (n : Nat) -> (x : X t) -> So (viable {t} n x)
> viability n x = Oh

> cxrvs : (t : Nat) -> (n : Nat) -> (i : Nat ** Vect i (X t))
> cxrvs t n = filter f (states t) where
>   f : (X t) -> Bool
>   f x = reachable {t} x && viable {t} n x

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

> admissiblesP : (x : X t) -> 
>                (v : So (viable {t} (S n) x)) -> 
>                (k : Nat ** Vect (S k) (Y t x))
> admissiblesP {t = t} {n = n} x v = filterTagP (admissible x) (outr s1) s6 where
>   s1 : (n : Nat ** Vect n Action)
>   s1 = (_ ** [Left, Right, Ahead])
>   s2 : (y : Y t x ** So (viable {t = S t} n (step t x y)))
>   s2 = viableSpec1 {t} {n} x v
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
>         (x : X t) -> 
>         (v : So (viable {t} (S n) x)) ->
>         (f : (y : Y t x ** So (viable {t = S t} n (step t x y)))-> Float) -> 
>         (k : Nat 
>          ** 
>          Vect (S k) ((y : Y t x ** So (viable {t = S t} n (step t x y))), Float)
>         )
> yfysP {t} n x v f = fmapP (pair (id,f)) s5 where
>   s1 : (k : Nat ** Vect (S k) (Y t x))
>   s1 = admissiblesP {t} {n} x v
>   s2 : (k : Nat ** Vect k (Y t x))
>   s2 = (_ ** outr s1)
>   s3 : Y t x -> Bool
>   s3 y = viable {t = S t} n (step t x y)
>   s4 : So (isAnyBy s3 s2)
>   s4 = believe_me Oh -- this should be more or less trivial
>   s5 : (k : Nat ** Vect (S k) (y : Y t x ** So (s3 y)))
>   s5 = filterTagP s3 (outr s2) s4

> MaxArgmax.max n x r v f = snd (maxP (outr (yfysP n x v f)))

> MaxArgmax.argmax n x r v f = fst (maxP (outr (yfysP n x v f)))

> MaxArgmax.maxSpec n x r v f yv = believe_me Oh -- this should be
>                                                -- granted by |maxP|

> MaxArgmax.argmaxSpec n x r v f = believe_me Oh -- this should be
>                                                -- granted by |maxP|

# Finite state

> -- nX : (m : Nat) -> (n : Nat) -> Nat
> FiniteState.nX t n = outl (cxrvs t n)

> xrvs : (t : Nat) -> (n : Nat) -> Vect (nX t n) (X t)
> xrvs t n = outr (cxrvs t n)

> -- index : (m : Nat) ->
> --         (n : Nat) ->
> --         (x : X ** (So (reachable m x), So (viable n x))) -> 
> --         Blt (nX m n)
> FiniteState.index {t} n xrv = xdi p x (xrvs t n) (believe_me Oh) where
>   p : X t -> X t -> Bool
>   p a b = column {t} a == column {t} b
>   x : X t
>   x = outl xrv

> -- xedni : (m : Nat) ->
> --         (n : Nat) ->
> --         Blt (nX m n) -> 
> --         (x : X ** (So (reachable m x), So (viable n x)))
> FiniteState.xedni {t} n i = (x ** (r,v)) where
>   x : X t
>   x = idx (xrvs t n) i
>   r : So (reachable {t} x)
>   r = believe_me Oh
>   v : So (viable {t} n x)  
>   v = believe_me Oh

> -- IndexSpec : (n' : Nat) ->
> --             (xrv : (x : X t ** (So (reachable x), So (viable n' x)))) -> 
> --             xrv = xedni n' (index n' xrv)
> FiniteState.IndexSpec n' xrv = believe_me Oh

> -- XedniSpec : (n : Nat) ->
> --             (i : Blt (nX t n)) -> 
> --             i = index n (xedni n i)
> FiniteState.XedniSpec n i = -- believe_me Oh
>   let res : (i = index n (xedni n i)) = believe_me Oh in res

  
# The computation:

> nSteps : Nat
> nSteps = 128

> ps : PolicySeq Z nSteps
> -- ps = backwardsInduction Z nSteps
> ps = tabulatedBackwardsInduction Z nSteps

> controls : (t : Nat) -> 
>            (n : Nat) -> 
>            (x : X t) -> 
>            (r : So (reachable {t} x)) -> 
>            (v : So (viable {t} n x)) ->
>            PolicySeq t n -> 
>            Vect n Action
> controls _ Z _ _ _ _ = Nil
> controls t (S n) x r v (p :: ps) =
>   ((outl y) :: (controls (S t) n x' r' v' ps)) where
>     yq : (a : Y t x ** So (viable {t = S t} n (step t x a)))
>     yq = p x r v
>     y : Y t x    
>     y = outl yq
>     x' : X (S t)
>     x' = step t x y
>     r' : So (reachable {t = S t} x')
>     r' = reachableSpec1 x r y
>     v' : So (viable {t = S t} n x')
>     v' = outr yq
           
> x0 : X Z
> x0 = (2 ** Oh)

> r0 : So (reachable {t = Z} x0)
> r0 = Oh

> v0 : So (viable {t = Z} nSteps x0)
> v0 = viability {t = Z} nSteps x0

> as : Vect nSteps Action 
> as = controls Z nSteps x0 r0 v0 ps
       
> main : IO ()
> main = putStrLn (show (toList as))
