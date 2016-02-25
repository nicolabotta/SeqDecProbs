> module Double


> import Data.So

> import Exists.Ops


> %default total


> ||| Non negative |Double|s
> data NonNegDouble : Type where
>   MkNonNegDouble : (x : Double) -> So (x >= 0.0) -> NonNegDouble

> Cast NonNegDouble Double where
>   cast (MkNonNegDouble x _) = x


> ||| |Double|s in [a,b]
> data GeLeDouble : Double -> Double -> Type where
>   MkGeLeDouble : {a : Double} -> {b : Double} ->
>                 (x : Double) -> So (a <= x) -> So (x <= b) -> GeLeDouble a b

> using (a, b : Double)
>   Cast (GeLeDouble a b) Double where
>     cast (MkGeLeDouble x _ _) = x


> |||
> data GeDouble : Double -> Type where
>   MkGeDouble : {a : Double} -> (x : Double) -> So (a <= x) -> GeDouble a

> using (a : Double)
>   Cast (GeDouble a) Double where
>     cast (MkGeDouble x _) = x


> |||
> data LeDouble : Double -> Type where
>   MkLeDouble : {a : Double} -> (x : Double) -> So (x <= a) -> LeDouble a

> using (a : Double)
>   Cast (LeDouble a) Double where
>     cast (MkLeDouble x _) = x



> using (p : Double -> Type)
>   Show (x : Double ** p x) where
>     show (x ** _) = show x

> using (p : Double -> Type)
>   Eq (x : Double ** p x) where
>     (==) (x ** _) (y ** _) = x == y
