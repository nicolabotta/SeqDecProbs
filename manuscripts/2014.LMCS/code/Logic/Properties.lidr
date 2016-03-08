> module Properties

> import Data.So

> %default total
> %access public export


> leibniz : (P : alpha -> Type) -> a1 = a2 -> P a1 -> P a2
> leibniz P Refl p = p


Reminder:

data So : Bool -> Type where
  Oh    : So True

> total soElim            :  (C : (b : Bool) -> So b -> Type) ->
>                            C True Oh                       ->
>                            (b : Bool) -> (s : So b) -> (C b s)
> soElim C coh True Oh    =  coh

> soFalseElim             :  So False -> a
> soFalseElim x           =  void (soElim C () False x)
>                            where
>                            C : (b : Bool) -> So b -> Type
>                            C True s = ()
>                            C False s = Void

> soTrue                  :  So b -> b = True
> soTrue {b = False} x    =  soFalseElim x
> soTrue {b = True}  x    =  Refl

> soTrueIntro                  :  b = True -> So b
> soTrueIntro {b = False} x  = void (trueNotFalse (sym x))
> soTrueIntro {b = True}  x  = Oh


> soIntro : (b : Bool) -> Dec (So b)
> soIntro False = (No  soFalseElim)
> soIntro  True = (Yes Oh)

