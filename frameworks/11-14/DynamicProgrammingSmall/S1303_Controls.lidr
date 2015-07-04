> module Controls

> import Data.So

> import Util.VectExtensions1

> import DynamicProgrammingSmall.S1301_Context

> %default total


> eqeq : Y t x -> Y t x -> Bool

> -- eqeqSpec1 : (y : Y t x) -> So (eqeq y y)
> eqeqSpec1 : (y : Y t x) -> So (Controls.eqeq y y)

These allow us to introduce the following abbreviations:

> isIn : Y t x -> (n : Nat ** Vect n (Y t x)) -> Bool
> -- isIn {t} {x} = VectExtensions1.isIn (Y t x) eqeq eqeqSpec1
> isIn {t} {x} = VectExtensions1.isIn (Y t x) Controls.eqeq Controls.eqeqSpec1

> lemma3 : (y : Y t x) ->
>          (p : Y t x -> Bool) ->
>          (ys : (n : Nat ** Vect n (Y t x))) ->
>          So (p y) ->
>          -- So (y `isIn` ys) ->
>          So (y `Controls.isIn` ys) ->
>          So (isAnyBy p ys)
> -- lemma3 {t} {x} = VectExtensions1.lemma3 (Y t x) eqeq eqeqSpec1
> lemma3 {t} {x} = VectExtensions1.lemma3 (Y t x) Controls.eqeq Controls.eqeqSpec1

> whole : (n : Nat ** Vect n (Y t x)) -> Type
> -- whole {t} {x} = VectExtensions1.whole (Y t x) eqeq eqeqSpec1 
> whole {t} {x} = VectExtensions1.whole (Y t x) Controls.eqeq Controls.eqeqSpec1 
