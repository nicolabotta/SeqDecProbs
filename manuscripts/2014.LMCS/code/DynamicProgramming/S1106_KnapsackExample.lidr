> module Main

> import Data.So
> import Data.Vect

> import BoundedNat.Blt
> import Vect.Ops
> import Util.Opt
> import DynamicProgramming.S1101_Context
> import DynamicProgramming.S1102_OptimalControls
> import DynamicProgramming.S1103_OptimalPolicies
> import DynamicProgramming.S1104_MaxArgmax
> import DynamicProgramming.S1105_BackwardsInduction


> %default total


# The context (example specific):

> lastItem : Nat

> nItems : Nat
> nItems = S lastItem

> values : Vect nItems Float

> %assert_total
> value : Blt nItems -> Float
> value = idx values

> weights : Vect nItems Float

> %assert_total
> weight : Blt nItems -> Float
> weight = idx weights

> capacity : Float
> capacity = 2.0

> Context.State = ((load  : Float ** So (load <= capacity)),
>              Blt nItems
>             )

> load : State -> Float
> load ((l ** _), _) = l

> item : State -> Blt nItems
> item (_, t) = t

> data Action = Take | Drop

> instance Show Action where
>   show Take = "T"
>   show Drop = "D"

> admissible : Action -> State -> Bool
> admissible Take x = load x + weight (item x) <= capacity
> admissible Drop x = True

> Context.Ctrl x = (a : Action ** So (admissible a x))

> max' : (x : State) -> (Ctrl x -> Float) -> (Ctrl x , Float)
> max' x f with (admissible Take x)
>   | True  = max2' ((Take ** believe_me Oh), f (Take ** believe_me Oh))
>                   ((Drop ** Oh), f (Drop ** Oh))
>   | False = ((Drop ** Oh), f (Drop ** Oh))

> MaxArgmax.max x f = snd (max' x f)

> MaxArgmax.argmax x f = fst (max' x f)

> MaxArgmax.maxSpec x f y = believe_me True

> MaxArgmax.argmaxSpec x f = believe_me True

> partial
> step' : (x : State) -> Ctrl x -> So (Blt.toNat (item x) < lastItem) -> State
> step' x (Take ** at) q = (x', incBlt {b = S lastItem} (snd x) (believe_me Oh)) where
>   x' : (load : Float ** So (load <= capacity))
>   x' = (load x + weight (item x) ** at)
> step' x (Drop ** ad) q = (fst x, incBlt {b = S lastItem} (snd x) (believe_me Oh))

> Context.step x y = step' x y (believe_me Oh)

> Context.reward x (Take ** _) _ = value (item x)
> Context.reward x (Drop ** _) _ = 0.0


# The computation:

> lastItem = 4

> values = [5.0,1.0,2.0,4.0,3.0]

> weights = [0.5,1.0,1.0,1.0,1.0]

> ps : PolicySeq nItems
> ps = backwardsInduction nItems

> controls : (n : Nat) -> State -> Vect n Policy -> Vect n Action
> controls Z _ _  = Nil
> controls (S m) x (p :: ps) =
>   ((getWitness (p x)) :: (controls m (step x (p x)) ps))

> x0 : State
> x0 = ((0.0 ** Oh), (Z ** Oh))

> as : Vect nItems Action
> as = controls nItems x0 ps

> main : IO ()
> main = putStrLn (show as)
