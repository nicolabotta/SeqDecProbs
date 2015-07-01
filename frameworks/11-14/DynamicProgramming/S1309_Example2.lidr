> module Main

> import Control.Monad.Identity
> import Data.So
> import Data.Vect
> import Effects
> import Effect.Exception
> import Effect.StdIO

> import Vect.Ops
> import Util.VectExtensions1
> import Logic.Postulates
> import Logic.Properties
> import Bool.Postulates
> import Float.Postulates
> import Float.Properties
> import Util.Opt
> import Util.Util
> import Exists.Ops
> import BoundedNat.Blt
> import EffectException
> import EffectStdIO

> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Reachability
> import DynamicProgramming.S1302_Viability
> import DynamicProgramming.S1302_Feasibility
> import DynamicProgramming.S1303_Controls
> import DynamicProgramming.S1303_OptimalPolicies
> import DynamicProgramming.S1303_Trajectories
> import DynamicProgramming.S1304_MaxArgmax
> import DynamicProgramming.S1305_BackwardsInduction 
> import DynamicProgramming.S1307_FiniteState
> import DynamicProgramming.S1308_TabulatedBackwardsInduction

> %assert_total


We re-implement 'S1306_Example2.lidr' with Tabulation and |M = Identity|

nSteps  |  user time / S1209_Example2  |  user time / S1309_Example2
1          0.044s                         0.020s
2          0.068s                         0.048s
3          0.080s                         0.048s
4          0.116s                         0.056s
5          0.128s                         0.096s
6          0.160s                         0.092s
7          0.180s                         0.108s
8          0.200s                         0.124s
9          0.232s                         0.164s
10         0.256s                         0.172s
11         0.292s                         0.184s
..
100        3.948s                         2.552s

The difference in runtime is probably a result of some more handwaved proofs in S1309_Ex2.

# The context:

> maxColumnO2 : Nat
> maxColumnO2 = 5

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

> instance Eq Action where
>   (==) Left   Left = True
>   (==) Left      _ = False
>   (==) Ahead Ahead = True
>   (==) Ahead     _ = False
>   (==) Right Right = True
>   (==) Right     _ = False

> instance Prelude.Show.Show Action where
>   show Left = "L"
>   show Ahead = "A"
>   show Right = "R"

> admissible : {t : Nat} -> X t -> Action -> Bool
> admissible {t} x Ahead = column {t} x == 0 || column {t} x == maxColumn
> admissible {t} x Left  = column {t} x <= maxColumnO2
> admissible {t} x Right = column {t} x >= maxColumnO2

> -- Y : (t : Nat) -> X t -> Type
> Context.Y t x = (a : Action ** So (admissible {t} x a))

> action : Y t x -> Action
> action (a ** _) = a

> -- M : Type -> Type
> Context.M = Identity

> -- Mmap : (a -> b) -> M a -> M b
> Context.Mmap = map

> -- Mret : a -> M a
> Context.Mret = return

> -- Mbind : M alpha -> (alpha -> M beta) -> M beta
> Context.Mbind = (>>=)

> -- step : (t : Nat) -> (x : X t) -> Y t x -> M (X (S t))
> Context.step t (Z   ** q) (Left ** aL) = Id (maxColumn ** Oh)
> Context.step t (S n ** q) (Left ** aL) = Id (n ** believe_me Oh) -- trivial
> Context.step t (n ** q) (Ahead ** aA) = Id (n ** q)
> Context.step t (n ** q) (Right ** aR) = if n == maxColumn 
>                                         then Id (Z ** Oh) 
>                                         else Id (S n ** believe_me Oh)

> -- reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Float
> Context.reward t x y x' = if column {t = S t} x' == Z
>                           then 1.0
>                           else if S (column {t = S t} x') == nColumns
>                                then 2.0
>                                else 0.0

> -- MisIn : X (S t) -> M (X (S t)) -> Bool
> Context.MisIn {t} x (Id x') = column {t = S t} x == column {t = S t} x'

> -- MallTrue : M Bool -> Bool
> Context.MareAllTrue (Id b) = b

> -- Mspec1 : (b : Bool) -> So (MareAllTrue (Mret b) == b)
> Context.Mspec1 = reflexive_Bool_eqeq 
> -- Context.Mspec1 True  = Oh 
> -- Context.Mspec1 False = Oh 

> -- Mspec2 : (mx : M (X (S t))) ->
> --          (p : X (S t) -> Bool) ->
> --          So (MareAllTrue (Mmap p mx)) ->
> --          (x : X (S t)) ->
> --          So (x `MisIn` mx) ->
> --          So (p x)
> Context.Mspec2 mx p q x xisinmx = believe_me Oh

> -- meas : M Float -> Float
> Context.meas (Id r) = r

> -- measMon : (f : X t -> Float) -> 
> --           (g : X t -> Float) -> 
> --           ((x : X t) -> So (f x <= g x)) ->
> --           (mx : M (X t)) -> 
> --           So (meas (Mmap f mx) <= meas (Mmap g mx))
> Context.measMon f g flteg mx = believe_me Oh

# Reachability:

> -- Reachability.reachable : X t -> Bool
> Reachability.reachable {t} x =
>   if column {t} x == 0 || column {t} x == maxColumn then True
>      else abs (column {t} x - maxColumnO2) >= t  

> -- Reachability.reachableSpec0 : 
> --   (x : X Z) -> 
> --   So (reachable x)
> Reachability.reachableSpec0 x = believe_me Oh

> -- Reachability.reachableSpec1 : 
> --   (x : X t) ->
> --   So (reachable x) ->
> --   (y : Y t x) ->
> --   (x' : X (S t)) ->
> --   So (x' `MisIn` (step t x y)) ->
> --   So (reachable {t = S t} x')
> Reachability.reachableSpec1 x r y x' x'in = believe_me Oh

> -- Reachability.reachableSpec2 : 
> --   (x' : X (S t)) -> 
> --   So (reachable {t = S t} x') ->
> --   (x : X t ** (y : Y t x ** (So (reachable x), So (x' `MisIn` (step t x y)))))
> Reachability.reachableSpec2 {t} x' rx' = believe_me Oh

# Viability:

> -- Viability.viable : (n : Nat) -> X t -> Bool
> Viability.viable {t} n x = True

> -- Viability.viableSpec0 : 
> --   (x : X t) -> 
> --   So (viable Z x)
> Viability.viableSpec0 x = Oh

> -- Viability.viableSpec1 : 
> --   (x : X t) -> 
> --   So (viable (S n) x) -> 
> --   -- (y : Y t x ** So (x' `MisIn` (step t x y)) -> So (viable {t = S t} n x'))
> --   (y : Y t x ** So (MareAllTrue (Mmap (viable {t = S t} n) (step t x y))))
> Viability.viableSpec1 {t} {n} x v = ((a ** believe_me Oh) ** believe_me Oh)
>   where a : Action
>         a = if column {t} x <= maxColumnO2 then Left else Right

> -- Viability.viableSpec2 : 
> --   (x : X t) -> 
> --   -- (y : Y t x ** So (x' `MisIn` (step t x y)) -> So (viable {t = S t} n x')) -> 
> --   (y : Y t x ** So (MareAllTrue (Mmap (viable {t = S t} n) (step t x y)))) ->
> --   So (viable (S n) x)
> Viability.viableSpec2 x (y ** v) = Oh

> viability : (t : Nat) -> (n : Nat) -> (x : X t) -> So (viable {t} n x)
> viability t n x = Oh

> cxrvs : (t : Nat) -> (n : Nat) -> (i : Nat ** Vect i (X t))
> cxrvs t n = filter f (states t) where
>   f : (X t) -> Bool
>   f x = reachable {t} x && viable {t} n x


# Controls

> -- eqeq : Y t x -> Y t x -> Bool
> Controls.eqeq y y' = action y == action y'

> -- eqeqSpec1 : (y : Y t x) -> So (eqeq y y)
> Controls.eqeqSpec1 y = believe_me Oh


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

> admissiblesP : (t : Nat) -> 
>                (n : Nat) -> 
>                (x : X t) -> 
>                (v : So (viable {t} (S n) x)) -> 
>                Sigma Nat (\k => Vect (S k) (Y t x))
> admissiblesP t n x v = filterTagP (admissible {t} x) (outr s1) s6 where 
>   s1 : (n : Nat ** Vect n Action)
>   s1 = (_ ** [Left, Ahead, Right])
>   s2 : (y : Y t x ** So (feasible n x y))
>   s2 = viability1 {t} {n} x v
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
>   s6 = lemma3 s3 (admissible {t} x) s1 s5 s4 
         
> yfysP : (t : Nat) -> 
>         (n : Nat) ->
>         (x : X t) -> 
>         (v : So (viable {t} (S n) x)) ->
>         (f : (y : Y t x ** So (feasible n x y))-> Float) -> 
>         Sigma Nat (\ k => Vect (S k) ((y : Y t x ** So (feasible n x y)), Float))

> yfysP t n x v f = fmapP (pair (id,f)) s5 where
>   s1 : Sigma Nat (\ k => Vect (S k) (Y t x))
>   s1 = admissiblesP t n x v
>   s2 : (k : Nat ** Vect k (Y t x))
>   s2 = (_ ** outr s1) -- normalize s1
>   -- postulate wys : whole ys ### non collapsible ...
>   postulate wys : (y : Y t x) -> So (y `Controls.isIn` s2)
>   s3 : Y t x -> Bool
>   s3 y = feasible n x y
>   s4 : So (isAnyBy s3 s2)
>   s4 = Controls.lemma3 y s3 s2 py (wys y) where
>     yv : (y' : Y t x ** So (s3 y'))
>     yv = viability1 x v
>     y : Y t x
>     y = outl yv
>     py : So (s3 y)
>     py = outr yv
>   s5 : (k : Nat ** Vect (S k) (y : Y t x ** So (s3 y)))
>   s5 = filterTagP s3 (outr s1) s4
         
> -- max : (n : Nat) ->
> --       (x : X t) -> 
> --       (r : So (reachable x)) -> 
> --       (v : So (viable (S n) x)) ->
> --       (f : (y : Y t x ** So (feasible n x y))-> Float) -> 
> --       Float
> MaxArgmax.max {t} n x r v f = snd (maxP {n = k} yfys) where
>   k : Nat
>   k = getWitness (yfysP t n x v f)
>   yfys : Vect (S k) ((y : Y t x ** So (feasible n x y)), Float)
>   yfys = getProof (yfysP t n x v f)

> -- argmax : (n : Nat) ->
> --          (x : X t) -> 
> --          (r : So (reachable x)) -> 
> --          (v : So (viable (S n) x)) ->
> --          (f : (y : Y t x ** So (feasible n x y))-> Float) -> 
> --          (y : Y t x ** So (feasible n x y))
> MaxArgmax.argmax {t} n x r v f = fst (maxP (getProof (yfysP t n x v f)))

> -- maxSpec : (n : Nat) -> 
> --           (x : X t) ->
> --           (r : So (reachable x)) -> 
> --           (v : So (viable (S n) x)) ->
> --           (f : (y : Y t x ** So (feasible n x y))-> Float) -> 
> --           (yv : (y : Y t x ** So (feasible n x y))) ->
> --           So (f yv <= max n x r v f)
> MaxArgmax.maxSpec n x r v f yv = believe_me Oh -- ?

> -- argmaxSpec : (n : Nat) -> 
> --              (x : X t) ->
> --              (r : So (reachable x)) -> 
> --              (v : So (viable (S n) x)) ->
> --              (f : (y : Y t x ** So (feasible n x y))-> Float) -> 
> --              So (f (argmax n x r v f) == max n x r v f)
> MaxArgmax.argmaxSpec n x r v f = believe_me Oh -- ?


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
> FiniteState.xedni {t} n i = (x ** (believe_me Oh, believe_me Oh)) where -- (x ** (r,v)) where
>   x : X t
>   x = idx (xrvs t n) i
>   -- r : So (reachable x)
>   -- r = believe_me Oh
>   -- v : So (viable n x)  
>   -- v = believe_me Oh

> -- IndexSpec : (n' : Nat) ->
> --             (xrv : (x : X t ** (So (reachable x), So (viable n' x)))) -> 
> --             xrv = xedni n' (index n' xrv)
> FiniteState.IndexSpec n' xrv = believe_me Oh

> -- XedniSpec : (n : Nat) ->
> --             (i : Blt (nX t n)) -> 
> --             i = index n (xedni n i)
> FiniteState.XedniSpec n i =
>   let res : (i = index n (xedni n i)) = believe_me Oh in res

  
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
>     yq : (a : Y t x ** So (feasible n x a))
>     yq = p x r v
>     y : Y t x    
>     y = outl yq
>     f : M (X (S t)) -> (X (S t))
>     f (Id x) = x
>     mx' : M (X (S t))
>     mx' = step t x y
>     x' : X (S t)
>     x' = f mx' 
>     r' : So (reachable {t = S t} x')
>     r' = reachableSpec1 {t = t} x r y x' (believe_me Oh)
>     v' : So (viable {t = S t} n x')
>     v' = Mspec2 {t = t} mx' (viable {t = S t} n) (getProof yq) x' (believe_me Oh) 


# The computation:

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getBlt nColumns
>      r0 <- pure (reachable {t = Z} x0)
>      v0 <- pure (viable {t = Z} nSteps x0)
>      case (r0 && v0) of
>        True  => do ps <- pure (tabulatedBackwardsInduction Z nSteps)
>                    as <- pure (controls Z nSteps x0 (believe_me Oh) (believe_me Oh) ps)
>                    putStrLn (show as)
>        False => putStr ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps\n")

> main : IO ()
> main = run computation


