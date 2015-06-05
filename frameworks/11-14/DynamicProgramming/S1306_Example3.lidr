> module Main

> import Control.Monad.Identity

> import BoundedNat.Blt
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
  

We re-implement 'S1206_Example3.lidr' with |M = Identity|


# The context:

> nColumns : Nat
> nColumns = 5

> valid : Nat -> Blt nColumns -> Bool
> valid t i = t /= 3 || outl i > 3

> -- X : Nat -> Set
> Context.X t = (i : Blt nColumns ** so (valid t i))

> column : X t -> Nat
> column x = outl (outl x)

> (==) : X t -> X t -> Bool
> (==) x x' = column x == column x'

> states : (t : Nat) -> (n : Nat ** Vect n (X t))
> states t = zs where
>   xs : Vect nColumns (Blt nColumns)
>   xs = toVect (\ i => i)
>   ys : (n : Nat ** Vect n (Blt nColumns))
>   ys = filter (valid t) xs
>   zs : (n : Nat ** Vect n (X t))
>   zs = (_ ** map f (outr ys)) where
>     f : Blt nColumns -> X t
>     f i = (i ** really_believe_me (valid t i))

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

> %assert_total
> admissible : X t -> Action -> Bool
> admissible {t} x Ahead = 
>   valid (S t) (outl x)
> admissible {t} x Left with (Blt.toNat (outl x))
>   | Z    =  False
>   | S m  =  valid (S t) (decBlt (outl x) {p}) where 
>               p : Blt.toNat (outl x) = S m
>               p = really_believe_me (refl {S m})
> admissible {t} x Right = 
>   S (column x) /= nColumns
>   &&
>   valid (S t) (incBlt (outl x) (really_believe_me {b=so (S (Blt.toNat (outl x)) < nColumns)} oh))

> -- Y : (t : Nat) -> X t -> Type
> Context.Y t x = (a : Action ** so (admissible x a))

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

> step' : Nat -> Action -> Nat
> step' (S i) Left  = i
> step' i     Ahead = i
> step' i     Right = S i
> --- dummy case, should never be called
> step' Z     Left  = Z

> step'Lemma : (x : X t) -> 
>              (a : Action) ->
>              so (admissible x a) ->
>              so (step' (column x) a < nColumns)
> step'Lemma x a q = really_believe_me oh

> -- step : (t : Nat) -> (x : X t) -> Y t x -> M (X (S t))
> Context.step t x y = Id ((i' ** p') ** (really_believe_me oh)) where
>   a : Action
>   a = outl y
>   i' : Nat
>   i' = step' (column x) a
>   p : so (admissible x a)
>   p = outr y
>   p' : so (i' < nColumns)
>   p' = step'Lemma x a p

> -- reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Float
> Context.reward t x y x' = if column {t = S t} x' == Z
>                           then 2.0
>                           else if S (column {t = S t} x') == nColumns
>                                then 1.0
>                                else 0.0

> -- MisIn : X (S t) -> M (X (S t)) -> Bool
> -- Context.MisIn x (Id x') = x == x'
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
> Context.Mspec2 mx p q x xisinmx = really_believe_me oh

> -- meas : M Float -> Float
> Context.meas (Id r) = r

> -- measMon : (f : X t -> Float) -> 
> --           (g : X t -> Float) -> 
> --           ((x : X t) -> so (f x <= g x)) ->
> --           (mx : M (X t)) -> 
> --           so (meas (Mmap f mx) <= meas (Mmap g mx))
> Context.measMon f g flteg mx = believe_me True


# Reachability defaults:

> -- ReachabilityDefaults.eqeq : X t -> X t -> Bool
> ReachabilityDefaults.eqeq x x' = column x == column x'

> -- ReachabilityDefaults.eqeqSpec1 : (x : X t) -> so (eqeq x x)
> ReachabilityDefaults.eqeqSpec1 x = believe_me oh
                                     
> pred : X t -> X (S t) -> Bool
> pred {t} x x' = 
>   (admissible x Left && 
>    ViabilityDefaults.eqeq {t = S t} (Id x') (step t x (Left ** really_believe_me (admissible x Left))))
>   ||
>   (admissible x Ahead && 
>    ViabilityDefaults.eqeq {t = S t} (Id x') (step t x (Ahead ** really_believe_me (admissible x Ahead))))
>   || 
>   (admissible x Right && 
>    ViabilityDefaults.eqeq {t = S t} (Id x') (step t x (Right ** really_believe_me (admissible x Right))))

> -- ReachabilityDefaults.preds : 
> --   X (S t) -> 
> --   (n : Nat ** Vect n (X t))
> ReachabilityDefaults.preds {t} x' = filter p (outr (states t)) where
>   p : X t -> Bool
>   p x = pred x x'

> -- ReachabilityDefaults.predsSpec1 : 
> --   (x : X t) ->
> --   (y : Y t x) ->
> --   (x' : X (S t)) ->
> --   so (x' `MisIn` step t x y) ->
> --   so (x `isIn` (preds x'))
> ReachabilityDefaults.predsSpec1 x y x' x'misinsteptxy = really_believe_me oh

> -- Reachability.predsSpec2 : 
> --   (x' : X (S t)) ->
> --   (x : X t) ->
> --   so (x `isIn` (preds x')) ->
> --   (y : Y t x ** so (x' `MisIn` step t x y))
> ReachabilityDefaults.predsSpec2 x' x xisinpredsx' = really_believe_me oh


# Viability defaults:

> -- ViabilityDefaults.eqeq : M (X t) -> M (X t) -> Bool
> -- ViabilityDefaults.eqeq (Id x) (Id x') = x == x'
> ViabilityDefaults.eqeq {t = t} (Id x) (Id x') = column {t = t} x == column {t = t} x'

> -- ViabilityDefaults.eqeqSpec1 : (x : M (X t)) -> so (eqeq x x)
> ViabilityDefaults.eqeqSpec1 (Id x) = really_believe_me oh

> -- ViabilityDefaults.succs : 
> --   X t -> 
> --   (n : Nat ** Vect n (M (X (S t))))
> ViabilityDefaults.succs {t} x = 
>   fmap (\ x => Id x) (filter (Main.pred x) (outr (states (S t))))

> -- ViabilityDefaults.succsSpec1 : 
> --   (x : X t) ->
> --   (y : Y t x) ->
> --   -- so ((step t x y) `isIn` (succs x))
> --   so (isIn {t = S t} (step t x y) (succs x))
> ViabilityDefaults.succsSpec1 {t} x y = really_believe_me {b=so (isIn {t = S t} (step t x y) (succs x))} oh

> -- ViabilityDefaults.succsSpec2 : 
> --   (x : X t) ->
> --   (mx' : M (X (S t))) ->
> --   -- so (mx' `isIn` (succs x)) ->
> --   so (isIn {t = S t} mx' (succs x)) ->
> --   (y : Y t x ** mx' = step t x y)
> ViabilityDefaults.succsSpec2 {t} x mx' mx'isinsuccsx =
>   really_believe_me {b=(y : Y t x ** mx' = step t x y)} (the Nat 42) -- obvious bogosity better than subtle


# Controls

> -- eqeq : Y t x -> Y t x -> Bool
> Controls.eqeq y y' = action y == action y'

> -- eqeqSpec1 : (y : Y t x) -> so (eqeq y y)
> Controls.eqeqSpec1 y = really_believe_me {b = so (eqeq y y)} oh


# Max, argmax

> eqeq : Action -> Action -> Bool
> eqeq Left  Left  = True
> eqeq Left  _     = False
> eqeq Ahead Ahead = True
> eqeq Ahead _     = False
> eqeq Right Right = True
> eqeq Right _     = False

> eqeqSpec1 : reflexive Action eqeq
> eqeqSpec1 = really_believe_me oh 

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
>                (v : so (viable (S n) x)) -> 
>                (k : Nat ** Vect (S k) (Y t x))
> admissiblesP {t = t} {n = n} x v = filterTagP (admissible x) (outr s1) s6 where 
>   s1 : (n : Nat ** Vect n Action)
>   s1 = (_ ** [Left, Ahead, Right])
>   s2 : (y : Y t x ** so (feasible n x y))
>   s2 = viability1 {t} {n} x v
>   s3 : Action
>   s3 = outl (outl s2)
>   s4 : so (s3 `isIn` s1)
>   s4 = really_believe_me {b=so (s3 `isIn` s1)} oh
>   -- |Action| should be in |Enum| and |s1| should be set to |[toEnum 0
>   -- ..]|. Then |s4| would follow from a lemma of the kind:
>   -- (Enum alpha) => (a : alpha) -> so (a `isIn` toVect [toEnum 0 ..])
>   s5 : so (admissible x s3)
>   s5 = outr (outl s2)
>   s6 : so (isAnyBy (admissible x) s1)
>   s6 = lemma3 s3 (admissible x) s1 s5 s4 
  
  
> yfysP : (n : Nat) ->
>         (x : X t) -> 
>         (v : so (viable (S n) x)) ->
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
> MaxArgmax.max n x r v f = snd (maxP (outr (really_believe_me $ yfysP n x v f)))

> -- argmax : (n : Nat) ->
> --          (x : X t) -> 
> --          (r : so (reachable x)) -> 
> --          (v : so (viable (S n) x)) ->
> --          (f : (y : Y t x ** so (feasible n x y))-> Float) -> 
> --          (y : Y t x ** so (feasible n x y))
> MaxArgmax.argmax n x r v f = fst (maxP (outr (yfysP n x v f)))

> -- maxSpec : (n : Nat) -> 
> --           (x : X t) ->
> --           (r : so (reachable x)) -> 
> --           (v : so (viable (S n) x)) ->
> --           (f : (y : Y t x ** so (feasible n x y))-> Float) -> 
> --           (yv : (y : Y t x ** so (feasible n x y))) ->
> --           so (f yv <= max n x r v f)
> MaxArgmax.maxSpec n x r v f yv = really_believe_me oh -- ?

> -- argmaxSpec : (n : Nat) -> 
> --              (x : X t) ->
> --              (r : so (reachable x)) -> 
> --              (v : so (viable (S n) x)) ->
> --              (f : (y : Y t x ** so (feasible n x y))-> Float) -> 
> --              so (f (argmax n x r v f) == max n x r v f)
> MaxArgmax.argmaxSpec n x r v f = really_believe_me oh -- ?


# The computation:

> nSteps : Nat
> nSteps = 8

> ps : PolicySeq Z nSteps
> ps = backwardsInduction Z nSteps

> x0 : X Z
> x0 = ((1 ** oh) ** oh)

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
> main = putStrLn (show (as, Val Z nSteps x0 r0 v0 ps))                             
