> module Main

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
> import DynamicProgramming.S1308_TabulatedBackwardsInduction


In this example we model a sequential decision problem similar to the
one of 'S1306_Example4'. Here, the transition function yields a certain
outcome for |t < T < Tmax| and |t > T| but at |t = T| the outcome is
uncertain.  Of course, such uncertainty informs the optimal policies for
|t < T|.

The example is meant to provide a stylized model of climate policy
selection under uncertainty.

The states (or colum indexes) represent climate change drivers. An
initial state in column 2, for instance, could denote a mean temperature
deviations (...) of |2 * dt| degrees where |dt| is a fixed
discretization parameter.

Rewards depend on the current state and on the control (action, option)
selected at that state. They are high at low temperature deviations and
decrease as the temperature deviation increases. Moving to low
temperature deviations (or keeping the deviation constnt) has a
cost:

  reward t x y x' = benefit t x - cost t x y

The idea is that, at any |t|, the costs of moving toward lower
temperature deviations or to maintain the current deviation exceed the
sum of the benefits that can be achieved in the future: 

  sum_(t' = t + 1 .. Tmax - 1) (benefit t' x' - cost t' x' A) 
  < 
  sum_(t' = t + 1 .. Tmax - 1) (benefit t' x - cost t' x A) 
  < 
  cost t x L 

where |x'| represents the state to the left of |x|. Thus, at each time,
there is no incentive (from a cost-benefit analysis viewpoint) to adopt
policies which aim at reducing temperature deviations.

The catch is that, at |t = T|, the outcome of the transition function is
uncertain, no matter which control is selected. At this time, there is a
non-zero probability that, no matter which control is selected, the next
state will be one of very high temperature deviations. Such probability
is low at low temperature deviations and high at high temperature
deviations. In other words, we model a tipping point at |t = T|.


# The model context:

> tempDev : X t -> Float

> benefit : (t : Nat) -> (x : X t) -> Float

> futureBenefits : (t : Nat) -> (x : X t) -> (n : Nat) -> Float

We are forced to defer the declaration of |cost| to the line immediately
before its definition to be able to enforce its totality :

> -- cost : (t : Nat) -> (x : X t) -> (y : Y t x) -> Float

> nSteps : Nat

> T : Nat

> prob : (t : Nat) -> X t -> (p : Float ** so (0.0 <= p && p <= 1.0))



# The context:
             
> maxColumn : Nat
> maxColumn = 5

> nColumns : Nat
> nColumns = S maxColumn

> -- X : Nat -> Type
> Context.X t = Blt nColumns

> column : X t -> Nat
> column = outl

> maxX : (t : Nat) -> X t
> maxX t = (maxColumn ** oh)

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
> admissible x Ahead = True
> admissible x Left  = toNat {b = nColumns} x > 0
> admissible x Right = toNat {b = nColumns} x < maxColumn

> -- Y : (t : Nat) -> X t -> Type
> Context.Y t x = (a : Action ** so (admissible x a))

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

> -- step : (t : Nat) -> (x : X t) -> Y t x -> M (X (S t))

> --- dummy case, should never be called
> Context.step t (Z ** q) (Left ** aL) =
> if t == T
> then normalizeBy eqeq (convComb p sp1 sp2)
> else sp2 where
>   eqeq : X (S t) -> X (S t) -> Bool
>   eqeq x x' = outl x == outl x'
>   p : Float
>   -- p = outl (prob t (Z ** q))
>   p = outl (prob t (Z ** believe_me oh))
>   sp1 : SimpleProb (X (S t))
>   sp1 = Mret (maxColumn ** oh)
>   sp2 : SimpleProb (X (S t))
>   sp2 = Mret (Z ** believe_me oh)

> Context.step t (S n ** q) (Left ** aL) = 
> if t == T
> then normalizeBy eqeq (convComb p sp1 sp2)
> else sp2 where
>   eqeq : X (S t) -> X (S t) -> Bool
>   eqeq x x' = outl x == outl x'
>   p : Float
>   -- p = outl (prob t (S n ** q))
>   p = outl (prob t (S n ** believe_me oh))
>   sp1 : SimpleProb (X (S t))
>   sp1 = Mret (maxColumn ** oh)
>   sp2 : SimpleProb (X (S t))
>   sp2 = Mret (n ** believe_me oh)

> Context.step t (n ** q) (Ahead ** aA) = 
> if t == T
> then normalizeBy eqeq (convComb p sp1 sp2)
> else sp2 where
>   eqeq : X (S t) -> X (S t) -> Bool
>   eqeq x x' = outl x == outl x'
>   p : Float
>   -- p = outl (prob t (n ** q))
>   p = outl (prob t (n ** believe_me oh))
>   sp1 : SimpleProb (X (S t))
>   sp1 = Mret (maxColumn ** oh)
>   sp2 : SimpleProb (X (S t))
>   -- sp2 = Mret (n ** q)
>   sp2 = Mret (n ** believe_me oh)

> Context.step t (n ** q) (Right ** aR) =
> if t == T
> then normalizeBy eqeq (convComb p sp1 sp2)
> else sp2 where
>   eqeq : X (S t) -> X (S t) -> Bool
>   eqeq x x' = outl x == outl x'
>   p : Float
>   -- p = outl (prob t (n ** q))
>   p = outl (prob t (n ** believe_me oh))
>   sp1 : SimpleProb (X (S t))
>   sp1 = Mret (maxColumn ** oh)
>   sp2 : SimpleProb (X (S t))
>   sp2 = Mret (S n ** believe_me oh)


> %assert_total
> cost : (t : Nat) -> (x : X t) -> (y : Y t x) -> Float
> cost t x (Right ** _) = 0.0
> cost t x (Ahead ** _) = 
>   -- if x == (maxX t)
>   if column x == column (maxX t)       
>   then 0.0
>   else w * (fb - fb') where
>     x' : X t
>     x' = (S (toNat {b = nColumns} x) ** believe_me oh)
>     fb : Float
>     fb = futureBenefits t x nSteps
>     fb' : Float
>     fb' = futureBenefits t x' nSteps
>     w : Float
>     w = 1.1
> cost t (S n ** q) (Left ** _) = 
>   -- cost t (S n ** q) (Ahead ** oh) + w * (fb' - fb) where
>   cost t (S n ** believe_me oh) (Ahead ** oh) + w * (fb' - fb) where  
>     x' : X t
>     x' = (n ** believe_me oh)
>     fb : Float
>     -- fb = futureBenefits t (S n ** q) nSteps
>     fb = futureBenefits t (S n ** believe_me oh) nSteps
>     fb' : Float
>     fb' = futureBenefits t x' nSteps
>     w : Float
>     w = 1.1
> --- dummy case, should never be called
> cost t (Z ** q) (Left ** _) = 0.0

> -- reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Float
> Context.reward t x y x' = benefit t x' - cost t x y

> -- MisIn : X (S t) -> M (X (S t)) -> Bool
> -- Context.MisIn x mx = elemBy (==) x (suppBy (==) mx)
> Context.MisIn x mx = elemBy eqeq x (suppBy eqeq mx) where  
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
> Context.measMon f g flteg mx = believe_me True


# Reachability:

> -- Reachability.reachable : X t -> Bool
> Reachability.reachable {t} x = True

> -- Reachability.reachableSpec0 : 
> --   (x : X Z) -> 
> --   so (reachable x)
> Reachability.reachableSpec0 x = oh

> -- Reachability.reachableSpec1 : 
> --   (x : X t) ->
> --   so (reachable x) ->
> --   (y : Y t x) ->
> --   (x' : X (S t)) ->
> --   so (x' `MisIn` (step t x y)) ->
> --   so (reachable {t = S t} x')
> Reachability.reachableSpec1 x r y x' x'in = oh

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
> Viability.viableSpec1 x v = believe_me oh

> -- Viability.viableSpec2 : 
> --   (x : X t) -> 
> --   -- (y : Y t x ** so (x' `MisIn` (step t x y)) -> so (viable {t = S t} n x')) -> 
> --   (y : Y t x ** so (MareAllTrue (Mmap (viable {t = S t} n) (step t x y)))) ->
> --   so (viable (S n) x)
> Viability.viableSpec2 x (y ** v) = oh

> cxrvs : (t : Nat) -> (n : Nat) -> (i : Nat ** Vect i (X t))
> cxrvs t n = filter f (states t) where
>   f : (X t) -> Bool
>   f x = reachable x && viable n x


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


# Finite state

> -- nX : (m : Nat) -> (n : Nat) -> Nat
> FiniteState.nX t n = outl (cxrvs t n)

> xrvs : (t : Nat) -> (n : Nat) -> Vect (nX t n) (X t)
> xrvs t n = outr (cxrvs t n)

> -- index : (m : Nat) ->
> --         (n : Nat) ->
> --         (x : X ** (so (reachable m x), so (viable n x))) -> 
> --         Blt (nX m n)
> FiniteState.index {t} n xrv = xdi p x (xrvs t n) (believe_me oh) where
>   p : X t -> X t -> Bool
>   p a b = column a == column b
>   x : X t
>   x = outl xrv

> -- xedni : (m : Nat) ->
> --         (n : Nat) ->
> --         Blt (nX m n) -> 
> --         (x : X ** (so (reachable m x), so (viable n x)))
> FiniteState.xedni {t} n i = (x ** (r,v)) where
>   x : X t
>   x = idx (xrvs t n) i
>   r : so (reachable x)
>   r = believe_me oh
>   v : so (viable n x)  
>   v = believe_me oh

> -- IndexSpec : (m : Nat) ->
> --             (n : Nat) ->
> --             (xrv : (x : X ** (so (reachable m x), so (viable n x)))) -> 
> --             xrv = xedni m n (index m n xrv)
> FiniteState.IndexSpec n xrv = believe_me oh

> -- XedniSpec : (m : Nat) ->
> --             (n : Nat) ->
> --             (i : Blt (nX m n)) -> 
> --             i = index m n (xedni m n i)
> FiniteState.XedniSpec n i = believe_me oh 


# The specific model

> -- tempDev : X t -> Float
> tempDev x = dx * (toFloat {b = nColumns} x) where
>   dx : Float
>   dx = 1.0

> -- benefit : (t : Nat) -> (x : X t) -> Float
> benefit t x = a - b * (toFloat {b = nColumns} x) where
>   a : Float
>   a = 1.0
>   b : Float
>   b = 1.0 / (toFloat {b = nColumns} (maxX t))

> -- futureBenefits : (t : Nat) -> (x : X t) -> (n : Nat) -> Float
> futureBenefits t x Z = 0.0
> futureBenefits t x (S n) = 
>   benefit (S t) x' + futureBenefits (S t) x' n where
>     x' : X (S t)
>     x' = (toNat {b = nColumns} x ** believe_me oh)

We are forced to move the declaration of |cost| to a point before the
implementation of |reward| (which calls |cost|) to be able to enforce
its totality :

> {-
> cost : (t : Nat) -> (x : X t) -> (y : Y t x) -> Float
> cost t x (Right ** _) = 0.0
> cost t x (Ahead ** _) = 
>   -- if x == (maxX t)
>   if column x == column (maxX t)       
>   then 0.0
>   else w * (fb - fb') where
>     x' : X t
>     x' = (S (toNat {b = nColumns} x) ** believe_me oh)
>     fb : Float
>     fb = futureBenefits t x nSteps
>     fb' : Float
>     fb' = futureBenefits t x' nSteps
>     w : Float
>     w = 1.1
> cost t x (Left ** _) with (column x)
>   | Z = 0.0 -- dummy case, should never be called
>   | S n = cost t x (Ahead ** oh) + w * (fb' - fb) where
>       x' : X t
>       x' = (n ** believe_me oh)
>       fb : Float
>       fb = futureBenefits t x nSteps
>       fb' : Float
>       fb' = futureBenefits t x' nSteps
>       w : Float
>       w = 1.1
> {-
> cost t (S n ** q) (Left ** _) =
>   cost t (S n ** q) (Ahead ** oh) + w * (fb' - fb) where
>     x' : X t
>     x' = (n ** believe_me oh)
>     fb : Float
>     fb = futureBenefits t (S n ** q) nSteps
>     fb' : Float
>     fb' = futureBenefits t x' nSteps
>     w : Float
>     w = 1.1
> --- dummy case, should never be called
> cost t (Z ** q) (Left ** _) = 0.0
> -}
> -}


> -- nSteps : Nat
> nSteps = 4

> -- T : Nat
> T = 2

> -- prob : (t : Nat) -> X t -> (p : Float ** so (0.0 <= p && p <= 1.0))
> prob t x =
>   (eps + (1 - eps) * (toFloat {b = nColumns} x) / 
>          (toFloat {b = nColumns}(maxX t)) 
>    ** 
>    believe_me oh) where 
>     eps : Float
>     eps = 0.1
 


# The computation:

> ps : PolicySeq Z nSteps
> ps = tabulatedBackwardsInduction Z nSteps

> x0 : X Z
> x0 = (1 ** oh)

> mxys : M (StateCtrlSeq Z nSteps)
> mxys = stateCtrlTrj Z nSteps x0 oh oh ps

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







