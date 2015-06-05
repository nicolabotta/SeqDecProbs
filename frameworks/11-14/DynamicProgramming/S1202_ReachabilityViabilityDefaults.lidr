> module ReachabilityViabilityDefaults


> import Logic.Properties
> import Exists.Ops
> import Util.VectExtensions1

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability


> %default total

We provide default implementation for |reachable| and |viable| that
fulfill the specifications required by "S1202_ReachabilityViability" on
the basis of the notions of successors and predecessors. These can be
formalized in terms of

> succs : X t -> (n : Nat ** Vect n (X (S t)))

> preds : X (S t) -> (n : Nat ** Vect n (X t))

Clients of this module are supposed to define |succs| and |preds| as to
be compatible with |step| and |Y|. We express the compatibility
conditions in terms of

> eqeq : X t -> X t -> Bool

> eqeqSpec1 : (x : X t) -> so (eqeq x x)

> isIn : X t -> (n : Nat ** Vect n (X t)) -> Bool
> isIn {t} = VectExtensions1.isIn (X t) eqeq eqeqSpec1

> lemma2 : (xs : (n : Nat ** Vect n (X t))) ->
>          so (not (isEmpty xs)) ->
>          (x : X t ** so (x `isIn` xs))
> lemma2 {t} = VectExtensions1.lemma2 (X t) eqeq eqeqSpec1

> lemma3 : (x : X t) ->
>          (p : X t -> Bool) ->
>          (xs : (n : Nat ** Vect n (X t))) ->
>          so (p x) ->
>          so (x `isIn` xs) ->
>          so (isAnyBy p xs)
> lemma3 {t} = VectExtensions1.lemma3 (X t) eqeq eqeqSpec1

> lemma6 : (p  : X t -> Bool) ->
>          (xs : (n : Nat ** Vect n (X t))) ->
>          so (isAnyBy p xs) ->
>          (x : X t ** (so (p x), so (x `isIn` xs)))
> lemma6 {t} = VectExtensions1.lemma6 (X t) eqeq eqeqSpec1

These are:

> succsSpec1 : (x : X t) ->
>              (y : Y t x) ->
>              so (step t x y `isIn` succs x)

> succsSpec2 : (x : X t) ->
>              (x' : X (S t)) ->
>              so (x' `isIn` succs x) ->
>              (y : Y t x ** x' = step t x y)

> predsSpec1 : (x : X t) ->
>              (y : Y t x) ->
>              so (x `isIn` preds (step t x y))

> predsSpec2 : (x' : X (S t)) ->
>              (x : X t) ->
>              so (x `isIn` preds x') ->
>              (y : Y t x ** x' = step t x y)
> 

If |succs| and |preds| fulfill the above specifications, default
definitions of |reachable| and |viable| can be given as follows:

> -- ReachabilityViability.reachable : X t -> Bool
> ReachabilityViability.reachable {t = Z} _ = True
> ReachabilityViability.reachable {t = S t} x' = isAnyBy reachable (preds x')

> -- ReachabilityViability.viable : (n : Nat) -> X t -> Bool
> ReachabilityViability.viable Z _ = True
> ReachabilityViability.viable {t} (S n) x = isAnyBy (viable {t = S t} n) (succs {t} x)

With the above definitions we have:

> -- ReachabilityViability.reachableSpec0 : 
> --   (x : X Z) -> 
> --   so (reachable x)
> ReachabilityViability.reachableSpec0 x = oh

> -- ReachabilityViability.reachableSpec1 : 
> --   (x : X t) ->
> --   so (reachable x) ->
> --   (y : Y t x) ->
> --   so (reachable {t = S t} (step t x y))
> ReachabilityViability.reachableSpec1 {t} x rmx y = step3 where
>   step1 : so (x `isIn` (preds (step t x y)))
>   step1 = predsSpec1 x y
>   step2 : so (isAnyBy reachable (preds (step t x y)))
>   step2 = lemma3 x reachable (preds (step t x y)) rmx step1
>   step3 : so (reachable (step t x y))
>   step3 = step2

> -- ReachabilityViability.reachableSpec2 : 
> --   (x' : X (S t)) -> 
> --   so (reachable {t = S t} x') ->
> --   (x : X t ** (y : Y t x ** (so (reachable x), x' = step t x y)))
> ReachabilityViability.reachableSpec2 {t = t} x' rx' = 
>   (x ** (y ** (xr, x'eq))) where
>     xrinpx' : (xx : X t ** (so (reachable xx), so (xx `isIn` (preds x'))))
>     xrinpx' = lemma6 reachable (preds x') rx'
>     x  : X t
>     x  = outl xrinpx'
>     xr : so (reachable x)
>     xr = fst (outr xrinpx')
>     xinpx' : so (x `isIn` (preds x'))
>     xinpx' = snd (outr xrinpx')
>     yx'eq : (yy : Y t x ** x' = step t x yy)
>     yx'eq = predsSpec2 x' x xinpx'
>     y : Y t x
>     y = outl yx'eq
>     x'eq : x' = step t x y
>     x'eq = outr yx'eq

and

> -- ReachabilityViability.viableSpec0 : (x : X t) -> so (viable Z x)
> ReachabilityViability.viableSpec0 x = oh
                                        

> -- ReachabilityViability.viableSpec1 : (x : X t) -> 
> --                                     so (viable (S n) x) -> 
> --                                     (y : Y t x ** so (viable {t = S t} n (step t x y)))

The idea is:

viable (S n) x
  = { def. }
isAnyBy (viable n) (succs x)  
  => { lemma6 }
(x' : X (S t) ** x' `isIn` (succs x) && viable n x')
  => { succsSpec2 }
(y : Y t x ** x' = step t x y)
  => { viable n x' }
(y : Y t x ** viable n (step t x y))

> ReachabilityViability.viableSpec1 {t} {n} x v = s11 where
>   s1 : so (isAnyBy (viable n) (succs x))
>   s1 = v
>   s2 : (xx : X (S t) ** 
>         (so (viable n xx), 
>          so (xx `isIn` succs x)
>         )
>        )
>   s2 = lemma6 (viable {t = S t} n) (succs x) s1
>   s3 : X (S t)
>   s3 = outl s2
>   s4 : so (s3 `isIn` (succs x))
>   s4 = snd (outr s2)
>   s5 : (yy : Y t x ** s3 = step t x yy)
>   s5 = succsSpec2 x s3 s4
>   s6 : Y t x
>   s6 = outl s5
>   s7 : so (viable n s3)
>   s7 = fst (outr s2)
>   s8 : s3 = step t x s6
>   s8 = outr s5
>   s9 : so (viable {t = S t} n (step t x s6))
>   s9 = leibniz (\ xSt => so (viable {t = S t} n xSt)) s8 s7
>   s11 : (yy : Y t x ** so (viable {t = S t} n (step t x yy)))
>   s11 = (s6 ** s9)

> -- ReachabilityViability.viableSpec2 : 
> --   (x : X t) -> 
> --   (y : Y t x ** so (viable {t = S t} n (step t x y))) ->
> --   so (viable (S n) x)
> ReachabilityViability.viableSpec2 {t} {n} x yv = step5 where
>   y : Y t x
>   y = outl yv
>   x' : X (S t)
>   x' = step t x y
>   p : X (S t) -> Bool
>   p = viable n
>   px' : so (viable n x')
>   px' = outr yv
>   xs' : (n : Nat ** Vect n (X (S t)))
>   xs' = succs x
>   x'isInxs' : so (x' `isIn` xs')
>   x'isInxs' = succsSpec1 x y
>   step4 : so (isAnyBy (viable n) xs')
>   step4 = lemma3 x' p (succs x) px' x'isInxs'
>   step5 : so (viable (S n) x)
>   step5 = step4
