> module Main

> -- import BoundedNat.Blt
> -- import Vect.Ops
> -- import Util.VectExtensions1
> -- import Logic.Postulates
> -- import Logic.Properties
> -- import Bool.Postulates
> -- import Float.Postulates
> import Float.Properties
> -- import Util.Opt
> -- import Util.Util
> import Prob.SimpleProb
> import Exists.Ops

> import DynamicProgramming.S1301_Context
> -- import DynamicProgramming.S1302_Reachability
> -- import DynamicProgramming.S1302_Viability
> -- import DynamicProgramming.S1302_Feasibility
> -- import DynamicProgramming.S1303_Controls
> -- import DynamicProgramming.S1303_OptimalPolicies
> -- import DynamicProgramming.S1303_Trajectories
> -- import DynamicProgramming.S1304_MaxArgmax
> -- import DynamicProgramming.S1305_BackwardsInduction
> -- import DynamicProgramming.S1308_TabulatedBackwardsInduction


# The model context:

> nSteps : Nat

> T : Nat

> prob : (t : Nat) -> X t -> (p : Float ** so (0.0 <= p && p <= 1.0))


# The context:

> nPlayers : Nat
> nPlayers = 6

> maxEmiss : Vect nPlayers Float
> maxEmiss = [1.0, 1.0, 1.0, 1.0, 1.0, 1.0]

> minEmiss : Vect nPlayers Float
> minEmiss = [0.0, 0.0, 0.0, 0.0, 0.0, 0.0]

> vulnCoeff : Vect nPlayers Float

> benefCoeff : Vect nPlayers (Float, Float)

> legal : (t : Nat) -> Vect nPlayers Float -> Bool
> legal t es = and (Vect.zipWith p es (zip minEmiss maxEmiss))
>                          where p : Float -> (Float, Float) -> Bool
>                                p e (min, max) = e <= max && e >= min


> -- X : Nat -> Type
> Context.X t = (es : Vect nPlayers Float ** so (legal t es))

> instance Eq a => Eq (Vect n a) where
>   (==) (x1 :: xs1) (x2 :: xs2) = (x1 == x2) && (xs1 == xs2)
>   (==) Nil Nil = True

> instance Eq a => Eq (v : Vect n a ** w) where
>   (==) (v1 ** p) (v2 ** q) = v1 == v2
   
> admissible : (t : Nat) -> X t -> X (S t) -> Bool
> admissible t xs xs' = True

> -- Y : (t : Nat) -> X t -> Type
> Context.Y t x = (x' : X (S t) ** so (admissible t x x'))

> -- M : Type -> Type
> Context.M = SimpleProb

> -- Mmap : (a -> b) -> M a -> M b
> Context.Mmap = map

> -- Mret : a -> M a
> Context.Mret = SimpleProb.return

> -- Mbind : M alpha -> (alpha -> M beta) -> M beta
> Context.Mbind = SimpleProb.bind

> -- step : (t : Nat) -> (x : X t) -> Y t x -> M (X (S t))
> Context.step t x y =
>   if t == T
>   then sp1 -- normalize (convComb p sp1 sp2)
>   else sp2 where
>     p : Float
>     p = outl (prob t x)
>     sp1 : SimpleProb (X (S t))
>     sp1 = Mret (minEmiss ** oh)
>     sp2 : SimpleProb (X (S t))
>     sp2 = Mret (outl y)

> benef : (Float, Float) -> Float -> Float

> -- reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Float
> Context.reward t x y x' = sum ((zipWith benef benefCoeff (outl x'))
>                                ++  (map  (* (sum (outl x'))) vulnCoeff))
