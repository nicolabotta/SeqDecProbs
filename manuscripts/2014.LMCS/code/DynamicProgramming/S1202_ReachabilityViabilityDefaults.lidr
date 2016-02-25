> module ReachabilityViabilityDefaults

> import Data.So
> import Data.Vect

> import Logic.Properties
> import Exists.Ops
> import Util.VectExtensions1

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability


> %default total

> ReachabilityViability.Reachable x = So (reachable x)
> ReachabilityViability.Viable n x = So (viable n x)

We provide default implementation for |reachable| and |viable| that
fulfill the specifications required by "S1202_ReachabilityViability" on
the basis of the notions of successors and predecessors. These can be
formalized in terms of

> succs : State t -> (n : Nat ** Vect n (State (S t)))

> preds : State (S t) -> (n : Nat ** Vect n (State t))

Clients of this module are supposed to define |succs| and |preds| as to
be compatible with |step| and |Ctrl|. We express the compatibility
conditions in terms of

> eqeq : State t -> State t -> Bool

> eqeqSpec1 : (x : State t) -> So (eqeq x x)

> isIn : State t -> (n : Nat ** Vect n (State t)) -> Bool
> isIn {t} = VectExtensions1.isIn (State t) eqeq eqeqSpec1

> lemma2 : (xs : (n : Nat ** Vect n (State t))) ->
>          So (not (isEmpty xs)) ->
>          (x : State t ** So (x `isIn` xs))
> lemma2 {t} = VectExtensions1.lemma2 (State t) eqeq eqeqSpec1

> lemma3 : (x : State t) ->
>          (p : State t -> Bool) ->
>          (xs : (n : Nat ** Vect n (State t))) ->
>          So (p x) ->
>          So (x `isIn` xs) ->
>          So (isAnyBy p xs)
> lemma3 {t} = VectExtensions1.lemma3 (State t) eqeq eqeqSpec1

> lemma6 : (p  : State t -> Bool) ->
>          (xs : (n : Nat ** Vect n (State t))) ->
>          So (isAnyBy p xs) ->
>          (x : State t ** (So (p x), So (x `isIn` xs)))
> lemma6 {t} = VectExtensions1.lemma6 (State t) eqeq eqeqSpec1

These are:

> succsSpec1 : (x : State t) ->
>              (y : Ctrl t x) ->
>              So (step t x y `isIn` succs x)

> succsSpec2 : (x : State t) ->
>              (x' : State (S t)) ->
>              So (x' `isIn` succs x) ->
>              (y : Ctrl t x ** x' = step t x y)

> predsSpec1 : (x : State t) ->
>              (y : Ctrl t x) ->
>              So (x `isIn` preds (step t x y))

> predsSpec2 : (x' : State (S t)) ->
>              (x : State t) ->
>              So (x `isIn` preds x') ->
>              (y : Ctrl t x ** x' = step t x y)
>

If |succs| and |preds| fulfill the above specifications, default
definitions of |reachable| and |viable| can be given as follows:

> -- ReachabilityViability.reachable : State t -> Bool
> ReachabilityViability.reachable {t = Z} _ = True
> ReachabilityViability.reachable {t = S t} x' = isAnyBy reachable (preds x')

> -- ReachabilityViability.viable : (n : Nat) -> State t -> Bool
> ReachabilityViability.viable Z _ = True
> ReachabilityViability.viable {t} (S n) x = isAnyBy (viable {t = S t} n) (succs {t} x)

With the above definitions we have:

> -- ReachabilityViability.reachableSpec0 :
> --   (x : State Z) ->
> --   So (reachable x)
> ReachabilityViability.reachableSpec0 x = Oh

> -- ReachabilityViability.reachableSpec1 :
> --   (x : State t) ->
> --   So (reachable x) ->
> --   (y : Ctrl t x) ->
> --   So (reachable {t = S t} (step t x y))
> ReachabilityViability.reachableSpec1 {t} x rmx y = step3 where
>   step1 : So (x `isIn` (preds (step t x y)))
>   step1 = predsSpec1 x y
>   step2 : So (isAnyBy ReachabilityViability.reachable (preds (step t x y)))
>   step2 = lemma3 x reachable (preds (step t x y)) rmx step1
>   step3 : So (reachable (step t x y))
>   step3 = step2

> -- ReachabilityViability.reachableSpec2 :
> --   (x' : State (S t)) -> Reachable x' ->
> --   (x : State t ** (Reachable x , (y : Ctrl t x ** x' = step t x y)))
> ReachabilityViability.reachableSpec2 {t = t} x' rx' =
>   (x ** (xr, (y ** x'eq))) where
>     xrinpx' : (xx : State t ** (So (reachable xx), So (xx `isIn` (preds x'))))
>     xrinpx' = lemma6 reachable (preds x') rx'
>     x  : State t
>     x  = outl xrinpx'
>     xr : So (reachable x)
>     xr = fst (outr xrinpx')
>     xinpx' : So (x `isIn` (preds x'))
>     xinpx' = snd (outr xrinpx')
>     yx'eq : (yy : Ctrl t x ** x' = step t x yy)
>     yx'eq = predsSpec2 x' x xinpx'
>     y : Ctrl t x
>     y = outl yx'eq
>     x'eq : x' = step t x y
>     x'eq = outr yx'eq

and

> -- ReachabilityViability.viableSpec0 : (x : State t) -> So (viable Z x)
> ReachabilityViability.viableSpec0 x = Oh


> -- ReachabilityViability.viableSpec1 : (x : State t) ->
> --                                     So (viable (S n) x) ->
> --                                     (y : Ctrl t x ** So (viable {t = S t} n (step t x y)))

The idea is:

viable (S n) x
  = { def. }
isAnyBy (viable n) (succs x)
  => { lemma6 }
(x' : State (S t) ** x' `isIn` (succs x) && viable n x')
  => { succsSpec2 }
(y : Ctrl t x ** x' = step t x y)
  => { viable n x' }
(y : Ctrl t x ** viable n (step t x y))

> ReachabilityViability.viableSpec1 {t} {n} x v = s11 where
>   s1 : So (isAnyBy (viable n) (succs x))
>   s1 = v
>   s2 : (xx : State (S t) **
>         (So (viable n xx),
>          So (xx `isIn` succs x)
>         )
>        )
>   s2 = lemma6 (viable {t = S t} n) (succs x) s1
>   s3 : State (S t)
>   s3 = outl s2
>   s4 : So (s3 `isIn` (succs x))
>   s4 = snd (outr s2)
>   s5 : (yy : Ctrl t x ** s3 = step t x yy)
>   s5 = succsSpec2 x s3 s4
>   s6 : Ctrl t x
>   s6 = outl s5
>   s7 : So (viable n s3)
>   s7 = fst (outr s2)
>   s8 : s3 = step t x s6
>   s8 = outr s5
>   s9 : So (viable {t = S t} n (step t x s6))
>   s9 = leibniz (\ xSt => So (viable {t = S t} n xSt)) s8 s7
>   s11 : (yy : Ctrl t x ** So (viable {t = S t} n (step t x yy)))
>   s11 = (s6 ** s9)

> -- ReachabilityViability.viableSpec2 :
> --   (x : State t) ->
> --   (y : Ctrl t x ** So (viable {t = S t} n (step t x y))) ->
> --   So (viable (S n) x)
> ReachabilityViability.viableSpec2 {t} {n} x yv = step5 where
>   y : Ctrl t x
>   y = outl yv
>   x' : State (S t)
>   x' = step t x y
>   p : State (S t) -> Bool
>   p = viable n
>   px' : So (viable n x')
>   px' = outr yv
>   xs' : (n : Nat ** Vect n (State (S t)))
>   xs' = succs x
>   x'isInxs' : So (x' `isIn` xs')
>   x'isInxs' = succsSpec1 x y
>   step4 : So (isAnyBy (viable n) xs')
>   step4 = lemma3 x' p (succs x) px' x'isInxs'
>   step5 : So (viable (S n) x)
>   step5 = step4
