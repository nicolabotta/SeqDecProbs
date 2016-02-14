> module Controls

> import Data.So
> import Data.Vect

> import Util.VectExtensions1
> import DynamicProgramming.S1201_Context


> %default total


> eqeq : Ctrl t x -> Ctrl t x -> Bool

> eqeqSpec1 : (y : Ctrl t x) -> So (Controls.eqeq y y)

These allow us to introduce the following abbreviations:

> isIn : Ctrl t x -> (n : Nat ** Vect n (Ctrl t x)) -> Bool
> isIn {t} {x} = VectExtensions1.isIn (Ctrl t x) Controls.eqeq Controls.eqeqSpec1

> lemma3 : (y : Ctrl t x) ->
>          (p : Ctrl t x -> Bool) ->
>          (ys : (n : Nat ** Vect n (Ctrl t x))) ->
>          So (p y) ->
>          So (y `Controls.isIn` ys) ->
>          So (isAnyBy p ys)
> lemma3 {t} {x} = VectExtensions1.lemma3 (Ctrl t x) Controls.eqeq Controls.eqeqSpec1

> whole : (n : Nat ** Vect n (Ctrl t x)) -> Type
> whole {t} {x} = VectExtensions1.whole (Ctrl t x) Controls.eqeq Controls.eqeqSpec1
