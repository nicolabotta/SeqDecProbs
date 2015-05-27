> module Properties

> import Data.So



> leibniz : (P : alpha -> Type) -> a1 = a2 -> P a1 -> P a2
> leibniz P Refl p = p

Reminder:

data So : Bool -> Type where
  Oh    : So True

> total soElim            :  (C : (b : Bool) -> So b -> Type) ->
>                            C True Oh                       ->
>                            (b : Bool) -> (s : So b) -> (C b s)
> soElim C coh True Oh  =  coh

> soFalseElim             :  So False -> a
> soFalseElim x           =  void (soElim C () False x)
>                            where
>                            C : (b : Bool) -> So b -> Type
>                            C True s = ()
>                            C False s = Void

> soTrue                  :  So b -> b = True
> soTrue {b = False} x    =  soFalseElim x
> soTrue {b = True}  x    =  Refl

> soContra1 : So b -> So (not b) -> alpha
> soContra1 {b = False} x _  =  soFalseElim x 
> soContra1 {b = True}  _ x  =  soFalseElim x 

> soAndContra1 : So (not b && b) -> a
> soAndContra1 {b = False} x = soFalseElim x
> soAndContra1 {b = True}  x = soFalseElim x

> soAndContra2 : So (b && not b) -> a
> soAndContra2 {b = False} x = soFalseElim x
> soAndContra2 {b = True}  x = soFalseElim x

> postulate soAndIntro : (p : alpha -> Bool) ->
>                        (q : beta -> Bool) -> 
>                        (a : alpha) ->
>                        (b : beta) ->
>                        So (p a) ->
>                        So (q b) ->
>                        So (p a && q b)

> postulate soAndElim1 : (p : alpha -> Bool) ->
>                        (q : beta -> Bool) -> 
>                        (a : alpha) ->
>                        (b : beta) ->
>                        So (p a && q b) -> 
>                        So (p a)

> postulate soAndElim2 : (p : alpha -> Bool) ->
>                        (q : beta -> Bool) -> 
>                        (a : alpha) ->
>                        (b : beta) ->
>                        So (p a && q b) -> 
>                        So (q b)

> {-

> a : Int

> pa : So (a < 2)

> b : Int

> qb : So (b > 3)

> paqb : So (a < 2 && b > 3)
> paqb = soAndIntro {p = \ x => x < 2} {q = \ y => y > 3} {a = a} {b = b} pa qb

> pa = soAndElim1 (\ x => x < 2) (\ y => y > 3) a b paqb

> qb = soAndElim2 (\ x => x < 2) (\ y => y > 3) a b paqb

> -}
