> module Main

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

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability
> import DynamicProgramming.S1203_Controls
> import DynamicProgramming.S1203_OptimalPolicies
> import DynamicProgramming.S1204_MaxArgmax
> import DynamicProgramming.S1205_BackwardsInduction
> import DynamicProgramming.S1202_ReachabilityViabilityDefaults

> %default total


We implement the case outlined in Fig. 3 of "S1200":


    8   | | | | | |
    7   | | | | | |
    6   | | | | | |
    5   | | | | | |
    4   | | | | | |
    3   |x|x|x|x| |
    2   | | | | | |
    1   | | | | | |
    0   | | | | | |

         0 1 2 3 4
  

For |t < 3| and |t > 3| all column indexes in |Blt 5| are valid. For |t
= 3|, however, only column 4 is valid.


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
>     f i = (i ** believe_me (valid t i))

> data Action = Left | Ahead | Right

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
>               p = believe_me oh
> admissible {t} x Right = 
>   S (column x) /= nColumns
>   &&
>   valid (S t) (incBlt (outl x) (believe_me oh))

> -- Y : (t : Nat) -> X t -> Type
> Context.Y t x = (a : Action ** so (admissible x a))

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
> step'Lemma x a q = believe_me oh

> 
> -- step : (t : Nat) -> (x : X t) -> Y t x -> X (S t)
> Context.step t x y = ((i' ** p') ** (believe_me oh)) where
>   a : Action
>   a = outl y
>   i' : Nat
>   i' = step' (column x) a
>   p : so (admissible x a)
>   p = outr y
>   p' : so (i' < nColumns)
>   p' = step'Lemma x a p
>   -- q' : so (valid t (i' ** p'))
>   -- q' = ?step1

> -- reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Float
> Context.reward t x y x' = if column {t = S t} x' == Z
>                           then 2.0
>                           else if S (column {t = S t} x') == nColumns
>                                then 1.0
>                                else 0.0


# Reachability, viability:

> -- eqeq : X t -> X t -> Bool
> ReachabilityViabilityDefaults.eqeq x x' = column x == column x'

> -- eqeqSpec1 : (x : X t) -> so (eqeq x x)
> ReachabilityViabilityDefaults.eqeqSpec1 x = believe_me oh

> {-
> pred : X t -> X (S t) -> Bool
> pred {t} x x' = 
>   (admissible x Left && 
>    eqeq {t = S t} x' (step t x (Left ** believe_me (admissible x Left))))
>   ||
>   (admissible x Ahead && 
>    eqeq {t = S t} x' (step t x (Ahead ** believe_me (admissible x Ahead))))
>   || 
>   (admissible x Right && 
>    eqeq {t = S t} x' (step t x (Right ** believe_me (admissible x Right))))
> -}

> pred : X t -> X (S t) -> Bool
> pred {t} x x' = 
>   (admissible x Left && 
>    eqeq {t = S t} x' (step t x (Left ** believe_me oh)))
>   ||
>   (admissible x Ahead && 
>    eqeq {t = S t} x' (step t x (Ahead ** believe_me oh)))
>   || 
>   (admissible x Right && 
>    eqeq {t = S t} x' (step t x (Right ** believe_me oh)))

> -- succs : X t -> (n : Nat ** Vect (X (S t)) n)
> ReachabilityViabilityDefaults.succs {t} x = filter (Main.pred x) (outr (states (S t)))

> -- preds : X (S t) -> (n : Nat ** Vect (X t) n)
> ReachabilityViabilityDefaults.preds {t} x' = filter p (outr (states t)) where
>   p : X t -> Bool
>   p x = pred x x'

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

# Controls

> -- eqeq : Y x t -> Y x t -> Bool
> Controls.eqeq ( Left ** _) ( Left ** _) = True
> Controls.eqeq ( Left ** _) (    _ ** _) = False
> Controls.eqeq (Ahead ** _) (Ahead ** _) = True
> Controls.eqeq (Ahead ** _) (    _ ** _) = False
> Controls.eqeq (Right ** _) (Right ** _) = True
> Controls.eqeq (Right ** _) (    _ ** _) = False

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
> 
> admissiblesP : (x : X t) -> 
>                (v : so (viable (S n) x)) -> 
>                (k : Nat ** Vect (S k) (Y t x))
> admissiblesP {t = t} {n = n} x v = filterTagP (admissible x) (outr s1) s6 where
>   s1 : (n : Nat ** Vect n Action)
>   s1 = (_ ** [Left, Ahead, Right])
>   s2 : (y : Y t x ** so (viable {t = S t} n (step t x y)))
>   s2 = viableSpec1 {t} {n} x v
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
>   %assert_total
>   s4 : so (isAnyBy s3 s2)
>   s4 = believe_me oh -- this should be more or less trivial
>   s5 : (k : Nat ** Vect (S k) (y : Y t x ** so (s3 y)))
>   s5 = filterTagP s3 (outr s1) s4

> MaxArgmax.max n x r v f = snd (maxP (outr (yfysP n x v f)))

> MaxArgmax.argmax n x r v f = fst (maxP (outr (yfysP n x v f)))

> MaxArgmax.maxSpec n x r v f yv = really_believe_me {b = so (f yv <= max n x r v f)} oh -- this should be
>                                                -- granted by |maxP|

> MaxArgmax.argmaxSpec n x r v f =
>   really_believe_me {b=so (f (argmax n x r v f) == max n x r v f)} oh -- this should be
>                                                -- granted by |maxP|

# The computation:

> nSteps : Nat
> nSteps = 8

> ps : PolicySeq Z nSteps
> ps = backwardsInduction Z nSteps

> controls : (t : Nat) -> 
>            (n : Nat) -> 
>            (x : X t) -> 
>            (r : so (reachable x)) -> 
>            (v : so (viable n x)) ->
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
> x0 = ((1 ** oh) ** oh)

> r0 : so (reachable {t = Z} x0)
> r0 = oh

> v0 : so (viable {t = Z} nSteps x0)
> v0 = oh

> as : Vect nSteps Action
> as = controls Z nSteps x0 r0 v0 ps

> main : IO ()
> main = putStrLn (show (as, Val Z nSteps x0 r0 v0 ps))

> -- -}
