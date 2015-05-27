> module Main

> import Control.Monad.Identity

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

> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Reachability
> import DynamicProgramming.S1302_Viability
> import DynamicProgramming.S1302_Feasibility
> import DynamicProgramming.S1303_Controls
> import DynamicProgramming.S1303_OptimalPolicies
> import DynamicProgramming.S1303_Trajectories
> import DynamicProgramming.S1304_MaxArgmax
> import DynamicProgramming.S1305_BackwardsInduction
> import DynamicProgramming.S1302_ReachabilityDefaults
> import DynamicProgramming.S1302_ViabilityDefaults

> %assert_total


We re-implement 'S1206_Example1.lidr' with |M = Identity|


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

> instance Eq Action where
>   (==) Left   Left = True
>   (==) Left      _ = False
>   (==) Ahead Ahead = True
>   (==) Ahead     _ = False
>   (==) Right Right = True
>   (==) Right     _ = False

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
> Context.step t (Z   ** q) (Left ** aL) = Id (maxColumn ** oh)
> Context.step t (S n ** q) (Left ** aL) = Id (n ** believe_me oh) -- trivial
> Context.step t (n ** q) (Ahead ** aA) = Id (n ** q)
> Context.step t (n ** q) (Right ** aR) = if n == maxColumn 
>                                         then Id (Z ** oh) 
>                                         else Id (S n ** believe_me oh)

> -- reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Float
> Context.reward t x y x' = if column {t = S t} x' == Z
>                           then 1.0
>                           else if S (column {t = S t} x') == nColumns
>                                then 2.0
>                                else 0.0

> -- MisIn : X (S t) -> M (X (S t)) -> Bool
> Context.MisIn {t = t} x (Id x') = column {t = S t} x == column {t = S t} x'

> -- MallTrue : M Bool -> Bool
> Context.MareAllTrue (Id b) = b

> -- Mspec1 : (b : Bool) -> so (MareAllTrue (Mret b) == b)
> Context.Mspec1 = reflexive_Bool_eqeq 
> -- Context.Mspec1 True  = oh 
> -- Context.Mspec1 False = oh 

> -- Mspec2 : (mx : M (X (S t))) ->
> --          (p : X (S t) -> Bool) ->
> --          so (MareAllTrue (Mmap p mx)) ->
> --          (x : X (S t)) ->
> --          so (x `MisIn` mx) ->
> --          so (p x)
> Context.Mspec2 mx p q x xisinmx = believe_me oh

> -- meas : M Float -> Float
> Context.meas (Id r) = r

> -- measMon : (f : X t -> Float) -> 
> --           (g : X t -> Float) -> 
> --           ((x : X t) -> so (f x <= g x)) ->
> --           (mx : M (X t)) -> 
> --           so (meas (Mmap f mx) <= meas (Mmap g mx))
> Context.measMon f g flteg mx = believe_me oh

# Reachability defaults:

> -- ReachabilityDefaults.eqeq : X t -> X t -> Bool
> ReachabilityDefaults.eqeq {t = t} x x' = column {t} x == column {t} x'

> -- ReachabilityDefaults.eqeqSpec1 : (x : X t) -> so (eqeq x x)
> ReachabilityDefaults.eqeqSpec1 x = believe_me oh

> pred : X t -> X (S t) -> Bool
> pred {t} x x' = 
>   (admissible {t} x Left && 
>    ViabilityDefaults.eqeq {t = S t} (Id x') (step t x (Left ** believe_me (admissible {t} x Left))))
>   ||
>   (admissible {t} x Ahead && 
>    ViabilityDefaults.eqeq {t = S t} (Id x') (step t x (Ahead ** believe_me (admissible {t} x Ahead))))
>   || 
>   (admissible {t} x Right && 
>    ViabilityDefaults.eqeq {t = S t} (Id x') (step t x (Right ** believe_me (admissible {t} x Right))))

> -- ReachabilityDefaults.preds : 
> --   X (S t) -> 
> --   (n : Nat ** Vect n (X t))
> ReachabilityDefaults.preds {t} x' = filter p (states t) where
>   p : X t -> Bool
>   p x = pred {t} x x'

> -- ReachabilityDefaults.predsSpec1 : 
> --   (x : X t) ->
> --   (y : Y t x) ->
> --   (x' : X (S t)) ->
> --   so (x' `MisIn` step t x y) ->
> --   so (x `isIn` (preds x'))
> ReachabilityDefaults.predsSpec1 x y x' x'misinsteptxy = believe_me oh

> -- Reachability.predsSpec2 : 
> --   (x' : X (S t)) ->
> --   (x : X t) ->
> --   so (x `isIn` (preds x')) ->
> --   (y : Y t x ** so (x' `MisIn` step t x y))
> ReachabilityDefaults.predsSpec2 x' x xisinpredsx' = believe_me oh


# Viability defaults:

> -- ViabilityDefaults.eqeq : M (X t) -> M (X t) -> Bool
> -- ViabilityDefaults.eqeq (Id x) (Id x') = x == x'
> ViabilityDefaults.eqeq (Id x) (Id x') = outl x == outl x'
> -- ViabilityDefaults.eqeq {t = t} (Id x) (Id x') = column {t = t} x == column {t = t} x'

> -- ViabilityDefaults.eqeqSpec1 : (x : M (X t)) -> so (eqeq x x)
> ViabilityDefaults.eqeqSpec1 (Id x) = believe_me oh

> -- ViabilityDefaults.succs : 
> --   X t -> 
> --   (n : Nat ** Vect n (M (X (S t))))
> ViabilityDefaults.succs {t} x = fmap (\ x => Id x) (filter (pred {t} x) (states (S t)))

> -- ViabilityDefaults.succsSpec1 : 
> --   (x : X t) ->
> --   (y : Y t x) ->
> --   -- so ((step t x y) `isIn` (succs x))
> --   so (isIn {t = S t} (step t x y) (succs x))
> ViabilityDefaults.succsSpec1 x y = believe_me oh

> -- ViabilityDefaults.succsSpec2 : 
> --   (x : X t) ->
> --   (mx' : M (X (S t))) ->
> --   -- so (mx' `isIn` (succs x)) ->
> --   so (isIn {t = S t} mx' (succs x)) ->
> --   (y : Y t x ** mx' = step t x y)
> ViabilityDefaults.succsSpec2 x mx' mx'isinsuccsx = believe_me oh


# Controls

> -- eqeq : Y t x -> Y t x -> Bool
> Controls.eqeq y y' = action y == action y'

> -- eqeqSpec1 : (y : Y t x) -> so (eqeq y y)
> Controls.eqeqSpec1 y = believe_me oh


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
>   s1 = (_ ** [Left, Ahead, Right])
>   s2 : (y : Y t x ** so (feasible n x y))
>   s2 = viability1 {t} {n} x v
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
>         (f : (y : Y t x ** so (feasible n x y))-> Float) -> 
>         (k : Nat 
>          ** 
>          Vect (S k) ((y : Y t x ** so (feasible n x y)), Float)
>         )

> yfysP {t} n x v f = fmapP (pair (id,f)) s5 where
>   s1 : (k : Nat ** Vect (S k) (Y t x))
>   s1 = admissiblesP x v
>   s2 : (k : Nat ** Vect k (Y t x))
>   s2 = (_ ** outr s1) -- normalize s1
>   -- postulate wys : whole ys ### non collapsible ...
>   postulate wys : (y : Y t x) -> so (y `Controls.isIn` s2)
>   s3 : Y t x -> Bool
>   s3 y = feasible n x y
>   s4 : so (isAnyBy s3 s2)
>   s4 = Controls.lemma3 y s3 s2 py (wys y) where
>     yv : (y' : Y t x ** so (s3 y'))
>     yv = viability1 x v
>     y : Y t x
>     y = outl yv
>     py : so (s3 y)
>     py = outr yv
>   s5 : (k : Nat ** Vect (S k) (y : Y t x ** so (s3 y)))
>   s5 = filterTagP s3 (outr s1) s4
         
> -- max : (n : Nat) ->
> --       (x : X t) -> 
> --       (r : so (reachable x)) -> 
> --       (v : so (viable (S n) x)) ->
> --       (f : (y : Y t x ** so (feasible n x y))-> Float) -> 
> --       Float
> MaxArgmax.max n x r v f = snd (maxP (getProof (yfysP n x v f)))

> -- argmax : (n : Nat) ->
> --          (x : X t) -> 
> --          (r : so (reachable x)) -> 
> --          (v : so (viable (S n) x)) ->
> --          (f : (y : Y t x ** so (feasible n x y))-> Float) -> 
> --          (y : Y t x ** so (feasible n x y))
> MaxArgmax.argmax n x r v f = fst (maxP (getProof (yfysP n x v f)))

> -- maxSpec : (n : Nat) -> 
> --           (x : X t) ->
> --           (r : so (reachable x)) -> 
> --           (v : so (viable (S n) x)) ->
> --           (f : (y : Y t x ** so (feasible n x y))-> Float) -> 
> --           (yv : (y : Y t x ** so (feasible n x y))) ->
> --           so (f yv <= max n x r v f)
> MaxArgmax.maxSpec n x r v f yv = believe_me oh -- ?

> -- argmaxSpec : (n : Nat) -> 
> --              (x : X t) ->
> --              (r : so (reachable x)) -> 
> --              (v : so (viable (S n) x)) ->
> --              (f : (y : Y t x ** so (feasible n x y))-> Float) -> 
> --              so (f (argmax n x r v f) == max n x r v f)
> MaxArgmax.argmaxSpec n x r v f = believe_me oh -- ?


# The computation:

> nSteps : Nat
> nSteps = 8

> ps : PolicySeq Z nSteps
> ps = backwardsInduction Z nSteps

> x0 : X Z
> x0 = (2 ** oh)

> r0 : so (reachable {t = Z} x0)
> r0 = oh

> v0 : so (viable {t = Z} nSteps x0)
> v0 = oh

> mxys : M (StateCtrlSeq Z nSteps)
> mxys = stateCtrlTrj Z nSteps x0 r0 v0 ps

> actions : (t : Nat) -> 
>           (n : Nat) -> 
>           M (StateCtrlSeq t n) ->
>           Vect n Action
> actions _ Z _ = Nil
> actions t (S n) (Id ((x ** y) :: xys)) 
>   = 
>   (outl y) :: (actions (S t) n (Id xys))

> as : Vect nSteps Action
> as = actions Z nSteps mxys

> main : IO ()
> main = putStrLn (show as)







