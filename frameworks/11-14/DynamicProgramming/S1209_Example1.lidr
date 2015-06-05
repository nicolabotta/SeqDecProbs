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

> import BoundedNat.Blt
> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability
> import DynamicProgramming.S1203_OptimalPolicies
> import DynamicProgramming.S1204_MaxArgmax
> import DynamicProgramming.S1205_BackwardsInduction
> import DynamicProgramming.S1202_ReachabilityViabilityDefaults
> import DynamicProgramming.S1207_FiniteState
> import DynamicProgramming.S1208_TabulatedBackwardsInduction

> %assert_total


We reimplement the example of |S1206_Example1.lidr| and compare the two
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

> -- eqeq : X t -> X t -> Bool
> ReachabilityViabilityDefaults.eqeq {t = t} x x' = column {t} x == column {t} x'

> -- eqeqSpec1 : (x : X t) -> so (eqeq x x)
> ReachabilityViabilityDefaults.eqeqSpec1 x = believe_me oh

> pred : X t -> X (S t) -> Bool
> pred {t} x x' =
>   (admissible {t} x Left && 
>    eqeq {t = S t} x' (step t x (Left ** believe_me (admissible {t} x Left))))
>   ||
>   (admissible {t} x Ahead && 
>    eqeq {t = S t} x' (step t x (Ahead ** believe_me (admissible {t} x Ahead))))
>   || 
>   (admissible {t} x Right && 
>    eqeq {t = S t} x' (step t x (Right ** believe_me (admissible {t} x Right))))

> -- succs : X t -> (n : Nat ** Vect (X (S t)) n)
> ReachabilityViabilityDefaults.succs {t} x = filter (pred {t} x) (states (S t))

> -- preds : X (S t) -> (n : Nat ** Vect (X t) n)
> ReachabilityViabilityDefaults.preds {t} x' = filter p (states t) where
>   p : X t -> Bool
>   p x = pred {t} x x'

> -- succsSpec1 : (x : X t) ->
> --              (y : Y t x) ->
> --              so ((step t x y) `isIn` (succs x))
> ReachabilityViabilityDefaults.succsSpec1 x y = believe_me oh -- ?

> -- succsSpec2 : (x : X t) ->
> --              (x' : X (S t)) ->
> --              so (x' `isIn` (succs x)) ->
> --              (y : Y t x ** x' = step t x y)
> ReachabilityViabilityDefaults.succsSpec2 x x' x'inCsuccsx = believe_me oh -- ?

> -- predsSpec1 : (x : X t) ->
> --              (y : Y t x) ->
> --              so (x `isIn` (preds (step t x y)))
> ReachabilityViabilityDefaults.predsSpec1 x y = believe_me oh -- ?

> -- predsSpec2 : (x' : X (S t)) ->
> --              (x : X t) ->
> --              so (x `isIn` (preds x')) ->
> --              (y : Y t x ** x' = step t x y)
> ReachabilityViabilityDefaults.predsSpec2 x' x xinCpredsx' = believe_me oh -- ?

> succsTh : (x : X t) -> so (not (isEmpty (succs {t} x)))
> succsTh x = believe_me oh -- this should be more or less trivial

> viability : (n : Nat) -> (x : X t) -> so (viable {t} n x)
> viability {t} Z x = viableSpec0 {t} x
> viability {t} (S n) k = step2 where  
>   step0 : so (not (isEmpty (succs {t} k)))
>   step0 = succsTh k
>   step1 : (x' : X (S t) ** so (isIn {t = S t} x' (succs {t} k)))
>   step1 = lemma2 {t = S t} (succs k) step0
>   step2 : so (isAnyBy (viable {t = S t} n) (succs {t} k))
>   step2 = lemma3 x' (viable {t = S t} n) (succs k) vnx' x'inCsuccsx where
>     x' : X (S t)
>     x' = outl step1
>     vnx' : so (viable {t = S t} n x')
>     vnx' = viability {t = S t} n x' -- induction step
>     x'inCsuccsx : so (isIn {t = S t} x' (succs {t} k))
>     x'inCsuccsx = outr step1
                    
> cxrvs : (t : Nat) -> (n : Nat) -> (i : Nat ** Vect i (X t))
> cxrvs t n = filter f (states t) where
>   f : (X t) -> Bool
>   f x = reachable {t} x && viable {t} n x

-- > rvability : (m : Nat) -> (n : Nat) -> so (not (emptyC (cxrvs m n)))
-- > rvability m n = believe_me oh -- ?


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
>   s6 = lemma3 s3 (admissible x) s1 s5 s4 

> yfysP : (n : Nat) ->
>         (x : X t) -> 
>         (v : so (viable {t} (S n) x)) ->
>         (f : (y : Y t x ** so (viable {t = S t} n (step t x y)))-> Float) -> 
>         (k : Nat 
>          ** 
>          Vect (S k) ((y : Y t x ** so (viable {t = S t} n (step t x y))), Float)
>         )
> yfysP {t} n x v f = fmapP (pair (id,f)) s5 where
>   s1 : (k : Nat ** Vect (S k) (Y t x))
>   s1 = admissiblesP x v
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

# Finite state

> -- nX : (m : Nat) -> (n : Nat) -> Nat
> FiniteState.nX t n = outl (cxrvs t n)

> xrvs : (t : Nat) -> (n : Nat) -> Vect (nX t n) (X t)
> xrvs t n = getProof (cxrvs t n)

> -- index : (n : Nat) ->
> --         (x : X t ** (so (reachable x), so (viable n x))) -> 
> --         Blt (nX t n)
> FiniteState.index {t} n xrv = xdi p x (xrvs t n) (believe_me oh) where
>   p : X t -> X t -> Bool
>   p a b = column {t} a == column {t} b
>   x : X t
>   x = outl xrv

> -- xedni : (m : Nat) ->
> --         (n : Nat) ->
> --         Blt (nX m n) -> 
> --         (x : X ** (so (reachable m x), so (viable n x)))
> FiniteState.xedni {t} n i = (x ** (r,v)) where
>   x : X t
>   x = idx (xrvs t n) i
>   r : so (reachable {t} x)
>   r = believe_me oh
>   v : so (viable {t} n x)  
>   v = believe_me oh

> -- IndexSpec : (n' : Nat) ->
> --             (xrv : (x : X t ** (so (reachable x), so (viable n' x)))) -> 
> --             xrv = xedni n' (index n' xrv)
> FiniteState.IndexSpec n' xrv = believe_me oh

> -- XedniSpec : (n : Nat) ->
> --             (i : Blt (nX t n)) -> 
> --             i = index n (xedni n i)
> FiniteState.XedniSpec n i =
>   let res : (i = index n (xedni n i)) = believe_me oh in res

  
# The computation:

> nSteps : Nat
> nSteps = 16

> ps : PolicySeq Z nSteps
> -- ps = backwardsInduction Z nSteps
> ps = tabulatedBackwardsInduction Z nSteps

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

> v0 : so (viable {t = 0} nSteps x0)
> v0 = viability {t = 0} nSteps x0

> as : Vect nSteps Action 
> as = controls Z nSteps x0 r0 v0 ps
       
> main : IO ()
> main = putStrLn (show as)
