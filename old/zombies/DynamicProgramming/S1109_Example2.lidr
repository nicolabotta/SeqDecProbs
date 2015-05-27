> module Main


> import Nat.Postulates
> import Float.Postulates
> import Float.Properties
> import BoundedNat.Blt
> import Logic.Properties
> import Vect.Ops
> import Util.Opt
> import DynamicProgramming.S1101_Context
> import DynamicProgramming.S1102_OptimalControls
> import DynamicProgramming.S1103_OptimalPolicies
> import DynamicProgramming.S1104_MaxArgmax
> import DynamicProgramming.S1105_BackwardsInduction
> import DynamicProgramming.S1107_FiniteState
> import DynamicProgramming.S1108_TabulatedBackwardsInduction


# The context (example specific):

> maxColumn : Nat
> maxColumn = 33

> nColumns : Nat
> nColumns = S maxColumn

> Context.X = Blt nColumns

> column : X -> Nat
> column = getWitness

> data Action = L | A | R

> instance Show Action where
>   show L = "L"
>   show A = "A"
>   show R = "R"

> Context.Y x = Action

> max' : (x : X) -> (Y x -> Float) -> (Y x, Float)
> max' x f = max3' (L, f L) (A, f A) (R, f R)

> MaxArgmax.max x f = snd (max' x f)

> MaxArgmax.argmax x f = fst (max' x f)

> MaxArgmax.maxSpec x f y = believe_me True

> MaxArgmax.argmaxSpec x f = believe_me True

> Context.step (Z   ** q) L = (maxColumn ** oh)
> Context.step (S n ** q) L = (n ** believe_me oh)                       
> -- Context.step (n ** q) A = (n ** q)
> -- this yields a user error (Internal error: "Codegen error: ...
> Context.step (n ** q) A = (n ** believe_me oh)
> Context.step (n ** q) R = if n == maxColumn 
>                           then (Z ** oh) 
>                           else (S n ** believe_me oh)

> Context.reward x y x' = if column x' == Z
>                         then 1.0
>                         else if S (column x') == nColumns
>                              then 2.0
>                              else 0.0


# |Finite X| context extensions:

> FiniteState.nX = nColumns

> FiniteState.index = id

> FiniteState.xedni = id

> FiniteState.IndexSpec x = refl

> FiniteState.XedniSpec i = refl


# The computation:

> nSteps : Nat
> nSteps = 28

> ps : PolicySeq nSteps
> ps = tabulatedBackwardsInduction nSteps

> controls : (n : Nat) -> X -> Vect n Policy -> Vect n Action
> controls Z _ _  = Nil
> controls (S m) x (p :: ps) = 
>   ((p x) :: (controls m (step x (p x)) ps))

> x0 : X
> x0 = (2 ** oh)

> as : Vect nSteps Action
> as = controls nSteps x0 ps

> main : IO ()
> main = putStrLn (show as)
