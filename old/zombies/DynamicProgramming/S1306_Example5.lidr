> module Main

> import Vect.Ops
> import Util.VectExtensions1
> import Logic.Postulates
> import Logic.Properties
> import Bool.Postulates
> import Float.Postulates
> import Float.Properties
> import Util.Opt
> import Util.Util
> import Prob.SimpleProb
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


We re-implement 'S1306_Example2.lidr' for |M = SimpleProb| and with the
transition function returning concentrated probability distributions.


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
> Context.M = SimpleProb

> -- Mmap : (a -> b) -> M a -> M b
> Context.Mmap = map

> -- Mret : a -> M a
> Context.Mret = SimpleProb.return

> -- Mbind : M alpha -> (alpha -> M beta) -> M beta
> Context.Mbind = SimpleProb.bind

we probably have to clean up a little bit here and require |M| to be an
instance of |Monad|. Then we will be able to use |return| and |>>=| and
|fmap| uniformly without having to introduce and define |Mret|, |Mbind|
and |Mmap|. In much the same way we might have to require |X t| to be in
|Eq|.

> -- step : (t : Nat) -> (x : X t) -> Y t x -> M (X (S t))
> Context.step t (Z   ** q) (Left ** aL) = Mret (maxColumn ** oh)
> Context.step t (S n ** q) (Left ** aL) = Mret (n ** believe_me oh) -- trivial
> Context.step t (n ** q) (Ahead ** aA) = Mret (n ** q)
> Context.step t (n ** q) (Right ** aR) = if n == maxColumn 
>                                         then Mret (Z ** oh) 
>                                         else Mret (S n ** believe_me oh)

> -- reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Float
> Context.reward t x y x' = if column {t = S t} x' == Z
>                           then 1.0
>                           else if S (column {t = S t} x') == nColumns
>                                then 2.0
>                                else 0.0

> -- MisIn : X (S t) -> M (X (S t)) -> Bool
> -- Context.MisIn x mx = elemBy (==) x (suppBy (==) mx)
> Context.MisIn {t = t} x mx = elemBy eqeq x (suppBy eqeq mx) where  
>   eqeq : X (S t) -> X (S t) -> Bool
>   eqeq {t = t} x x' = column {t = S t} x == column {t = S t} x'

> -- MallTrue : M Bool -> Bool
> Context.MareAllTrue mx = all ((==) True) (suppBy (==) mx)

> -- Mspec1 : (b : Bool) -> so (MareAllTrue (Mret b) == b)
> -- Context.Mspec1 = reflexive_Bool_eqeq 
> Context.Mspec1 True  = oh 
> Context.Mspec1 False = oh 

> -- Mspec2 : (mx : M (X (S t))) ->
> --          (p : X (S t) -> Bool) ->
> --          so (MareAllTrue (Mmap p mx)) ->
> --          (x : X (S t)) ->
> --          so (x `MisIn` mx) ->
> --          so (p x)
> Context.Mspec2 mx p q x xisinmx = believe_me oh

> -- meas : M Float -> Float
> Context.meas = eValue

> -- measMon : (f : X t -> Float) -> 
> --           (g : X t -> Float) -> 
> --           ((x : X t) -> so (f x <= g x)) ->
> --           (mx : M (X t)) -> 
> --           so (meas (Mmap f mx) <= meas (Mmap g mx))
> Context.measMon f g flteg mx = believe_me oh


# Reachability:

> -- Reachability.reachable : X t -> Bool
> Reachability.reachable {t} x =
>   if column x == 0 || column x == maxColumn then True
>      else abs (column x - maxColumnO2) >= t  

> -- Reachability.reachableSpec0 : 
> --   (x : X Z) -> 
> --   so (reachable x)
> Reachability.reachableSpec0 x = believe_me oh

> -- Reachability.reachableSpec1 : 
> --   (x : X t) ->
> --   so (reachable x) ->
> --   (y : Y t x) ->
> --   (x' : X (S t)) ->
> --   so (x' `MisIn` (step t x y)) ->
> --   so (reachable {t = S t} x')
> Reachability.reachableSpec1 x r y x' x'in = believe_me oh

> -- Reachability.reachableSpec2 : 
> --   (x' : X (S t)) -> 
> --   so (reachable {t = S t} x') ->
> --   (x : X t ** (y : Y t x ** (so (reachable x), so (x' `MisIn` (step t x y)))))
> Reachability.reachableSpec2 {t} x' rx' = believe_me oh

# Viability:

> -- Viability.viable : (n : Nat) -> X t -> Bool
> Viability.viable n x = True

> -- Viability.viableSpec0 : 
> --   (x : X t) -> 
> --   so (viable Z x)
> Viability.viableSpec0 x = oh

> -- Viability.viableSpec1 : 
> --   (x : X t) -> 
> --   so (viable (S n) x) -> 
> --   -- (y : Y t x ** so (x' `MisIn` (step t x y)) -> so (viable {t = S t} n x'))
> --   (y : Y t x ** so (MareAllTrue (Mmap (viable {t = S t} n) (step t x y))))
> Viability.viableSpec1 x v = ((a ** believe_me oh) ** believe_me oh)
>   where
>   a : Action
>   a = if column x <= maxColumnO2 then Left else Right

> -- Viability.viableSpec2 : 
> --   (x : X t) -> 
> --   -- (y : Y t x ** so (x' `MisIn` (step t x y)) -> so (viable {t = S t} n x')) -> 
> --   (y : Y t x ** so (MareAllTrue (Mmap (viable {t = S t} n) (step t x y)))) ->
> --   so (viable (S n) x)
> Viability.viableSpec2 x (y ** v) = oh

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
>   s4 = believe_me oh 
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
> MaxArgmax.max n x r v f = snd (maxP (outr (yfysP n x v f)))

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

> r0 : so (reachable x0)
> r0 = oh

> v0 : so (viable nSteps x0)
> v0 = oh

> mxys : M (StateCtrlSeq Z nSteps)
> mxys = stateCtrlTrj Z nSteps x0 r0 v0 ps

> actions : (t : Nat) -> 
>           (n : Nat) -> 
>           M (StateCtrlSeq t n) ->
>           (m : Nat ** Vect m (Vect n Action))
> actions _ Z _ = (_ ** Nil)
> actions t (S n) (SP scss) = (length step2 ** fromList step2) where
>   step1 : List (StateCtrlSeq t (S n))
>   step1 = map fst scss
>   step2 : List (Vect (S n) Action)
>   step2 = map (f t (S n)) step1 where
>     f : (t' : Nat) -> 
>         (n' : Nat) ->
>         StateCtrlSeq t' n' -> 
>         Vect n' Action
>     f _ Z _ = Nil
>     f t' (S n') ((x ** y) :: xys)
>       =
>       (outl y) :: (f (S t') n' xys)

> as : (m : Nat ** Vect m (Vect nSteps Action))
> as = actions Z nSteps mxys

> main : IO ()
> main = putStrLn (show (outr as))







