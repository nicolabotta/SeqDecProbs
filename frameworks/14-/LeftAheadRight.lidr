> module LeftAheadRight

> import Data.Fin
> import Control.Isomorphism

> import Finite
> import FiniteOperations
> import FiniteProperties
> import Sigma

> %default total
> %access public export
> %auto_implicits off


> ||| Left, Ahead or Right
> data LeftAheadRight = Left | Ahead | Right

> implementation Eq LeftAheadRight where
>   (==) Left   Left = True
>   (==) Left      _ = False
>   (==) Ahead Ahead = True
>   (==) Ahead     _ = False
>   (==) Right Right = True
>   (==) Right     _ = False

> implementation Show LeftAheadRight where
>   show Left  = "L"
>   show Ahead = "A"
>   show Right = "R"

LeftAheadRight is finite:

> to : LeftAheadRight -> Fin 3
> to Left  =        FZ
> to Ahead =     FS FZ
> to Right = FS (FS FZ)

> from : Fin 3 -> LeftAheadRight
> from             FZ   = Left
> from         (FS FZ)  = Ahead
> from     (FS (FS FZ)) = Right
> from (FS (FS (FS k))) = absurd k

> toFrom : (k : Fin 3) -> to (from k) = k
> toFrom             FZ   = Refl
> toFrom         (FS FZ)  = Refl
> toFrom     (FS (FS FZ)) = Refl
> toFrom (FS (FS (FS k))) = absurd k

> fromTo : (a : LeftAheadRight) -> from (to a) = a
> fromTo Left  = Refl
> fromTo Ahead = Refl
> fromTo Right = Refl

> finiteLeftAheadRight : Finite LeftAheadRight
> finiteLeftAheadRight = MkSigma 3 (MkIso to from toFrom fromTo)
> %freeze finiteLeftAheadRight


LeftAheadRight is non empty:

> cardNotZLeftAheadRight : CardNotZ finiteLeftAheadRight
> cardNotZLeftAheadRight = cardNotZLemma finiteLeftAheadRight Left
> %freeze cardNotZLeftAheadRight
