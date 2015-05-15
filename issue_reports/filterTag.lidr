> module Main

> import Data.Vect
> import Effects
> import Effect.Exception
> import Effect.StdIO
> import Decidable.Order

> %default total

> Dec1 : {A : Type} -> (P : A -> Type) -> Type
> Dec1 {A} P = (a : A) -> Dec (P a) 

> ||| Filters a vector on a decidable property and pairs elements with proofs
> filterTag : {A : Type} ->
>             {P : A -> Type} ->
>             Dec1 P ->
>             Vect n A -> 
>             Sigma Nat (\ m => Vect m (Sigma A P))
> filterTag d1P Nil = (Z ** Nil)
> filterTag d1P (a :: as) with (filterTag d1P as)
>   | (_ ** tail) with (d1P a)
>     | (Yes p)     = (_ ** (a ** p) :: tail)
>     | (No contra) = (_ ** tail)

> v : Vect 5 Nat
> v = [1,2,3,0,5]

> P : Nat -> Type
> P n = LTE n 2

> dP : (n : Nat) -> Dec (P n)
> dP n = lte n 2

> v' : (n : Nat ** Vect n (Sigma Nat P))
> v' = filterTag dP v


> computation : { [STDIO] } Eff ()
> computation =
>   do putStrLn (show v)
>      v' <- pure (map Sigma.getWitness (Sigma.getProof v'))
>      putStrLn (show v')

> main : IO ()
> main = run computation 
