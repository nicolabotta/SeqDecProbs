> module Float


> import Data.So

> import Exists.Ops


> %default total


> ||| Non negative |Float|s
> data NonNegFloat : Type where
>   MkNonNegFloat : (x : Float) -> So (x >= 0.0) -> NonNegFloat

> instance Cast NonNegFloat Float where
>   cast (MkNonNegFloat x _) = x


> ||| |Float|s in [a,b]
> data GeLeFloat : Float -> Float -> Type where
>   MkGeLeFloat : {a : Float} -> {b : Float} -> 
>                 (x : Float) -> So (a <= x) -> So (x <= b) -> GeLeFloat a b

> using (a, b : Float) 
>   instance Cast (GeLeFloat a b) Float where
>     cast (MkGeLeFloat x _ _) = x


> ||| 
> data GeFloat : Float -> Type where
>   MkGeFloat : {a : Float} -> (x : Float) -> So (a <= x) -> GeFloat a

> using (a : Float) 
>   instance Cast (GeFloat a) Float where
>     cast (MkGeFloat x _) = x


> ||| 
> data LeFloat : Float -> Type where
>   MkLeFloat : {a : Float} -> (x : Float) -> So (x <= a) -> LeFloat a

> using (a : Float) 
>   instance Cast (LeFloat a) Float where
>     cast (MkLeFloat x _) = x



> using (p : Float -> Type)
>   instance Show (x : Float ** p x) where
>     show (x ** _) = show x

> using (p : Float -> Type)
>   instance Eq (x : Float ** p x) where
>     (==) (x ** _) (y ** _) = x == y





