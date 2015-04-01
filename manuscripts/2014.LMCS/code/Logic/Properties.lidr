> module Properties

> leibniz : (P : alpha -> Type) -> a1 = a2 -> P a1 -> P a2
> leibniz P refl p = p

Reminder:

data so : Bool -> Type where
  oh    : so True

> total soElim            :  (C : (b : Bool) -> so b -> Type) ->
>                            C True oh                       ->
>                            (b : Bool) -> (s : so b) -> (C b s)
> soElim C coh .True .oh  =  coh

> soFalseElim             :  so False -> a
> soFalseElim x           =  FalseElim (soElim C () False x)
>                            where
>                            C : (b : Bool) -> so b -> Type
>                            C True s = ()
>                            C False s = _|_

> soTrue                  :  so b -> b = True
> soTrue {b = False} x    =  soFalseElim x
> soTrue {b = True}  x    =  refl

> soTrueIntro                  :  b = True -> so b
> soTrueIntro {b = False} x  = FalseElim (trueNotFalse (sym x))
> soTrueIntro {b = True}  x  = oh


> soIntro : (b : Bool) -> Dec (so b)
> soIntro False = (No  soFalseElim)
> soIntro  True = (Yes oh)

