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

> nColumns : Nat
> nColumns = 5

> Context.X = Blt nColumns

> column : X -> Nat
> column = getWitness

> data Pos = Left | Right | Middle 

> instance Eq Pos where
>   (==) Left Left = True
>   (==) Left _ = False
>   (==) Right Right = True
>   (==) Right _ = False
>   (==) Middle Middle = True
>   (==) Middle _ = False

> pos : (x : X) -> Pos
> pos x = if column x == 0
>         then Left
>         else if (S (column x)) == nColumns
>              then Right
>              else Middle

> data Action = L | A | R

> instance Show Action where
>   show L = "L"
>   show A = "A"
>   show R = "R"

> data AreAdmissible : Action -> Pos -> Type where
>   lm : AreAdmissible L Middle
>   lr : AreAdmissible L Right
>   al : AreAdmissible A Left
>   am : AreAdmissible A Middle
>   ar : AreAdmissible A Right
>   rl : AreAdmissible R Left
>   rm : AreAdmissible R Middle

> Context.Y x = (a : Action ** AreAdmissible a (pos x))

> max' : (x : X) -> (Y x -> Float) -> (Y x , Float)
> max' x f = maxHelp (pos x) f 
>   where
>   maxHelp               : (p : Pos) -> 
>                           ((a : Action ** AreAdmissible a p) -> Float) ->
>                           ((a : Action ** AreAdmissible a p), Float)
>   maxHelp  Left    f    =    max2' ((A ** al), (f (A ** al))) 
>                                    ((R ** rl), (f (R ** rl)))
>   maxHelp  Right   f    =    max2' ((L ** lr), (f (L ** lr))) 
>                                    ((A ** ar), (f (A ** ar)))
>   maxHelp  Middle  f    =    max3' ((L ** lm), (f (L ** lm))) 
>                                    ((A ** am), (f (A ** am))) 
>                                    ((R ** rm), (f (R ** rm)))
  
> MaxArgmax.max x f = snd (max' x f)

> MaxArgmax.argmax x f = fst (max' x f)

> MaxArgmax.maxSpec x f y = believe_me True

> MaxArgmax.argmaxSpec x f = believe_me True

> step' : Nat -> Action -> Nat
> step' (S i) L = i
> step' i     A = i
> step' i     R = S i
> step' Z     L = Z  -- should never be called!

> step'Lemma : (x : X) -> 
>              (a : Action) ->
>              AreAdmissible a (pos x) ->
>              so (step' (column x) a < nColumns)
> step'Lemma x a asm = believe_me True

> Context.step x y = (x' ** p') where
>   a : Action
>   a = getWitness y
>   x' : Nat
>   x' = step' (column x) a
>   apxAreAdmissible : AreAdmissible a (pos x)
>   apxAreAdmissible = believe_me oh -- getProof y
>   p' : so (x' < nColumns)
>   p' = step'Lemma x a apxAreAdmissible

> Context.reward x y x' = if column x' == Z
>                         then 1.0
>                         else if S (column x') == nColumns
>                           then 2.0
>                           else 0.0


# |Finite X| context extensions:

> FiniteState.nX = nColumns

> FiniteState.index = id

> FiniteState.xedni = id

> FiniteState.IndexSpec x = refl

> FiniteState.XedniSpec i = refl


# The computation:

> nSteps : Nat
> nSteps = 6

> ps : PolicySeq nSteps
> -- ps = backwardsInduction nSteps
> ps = tabulatedBackwardsInduction nSteps

> controls : (n : Nat) -> X -> Vect n Policy -> Vect n Action
> controls Z _ _  = Nil
> controls (S m) x (p :: ps) = 
>   ((getWitness (p x)) :: (controls m (step x (p x)) ps))

> x0 : X
> x0 = (1 ** oh)

> as : Vect nSteps Action
> as = controls nSteps x0 ps

> main : IO ()
> main = putStrLn (show as)
