> module ReachabilityDefaults


> import Logic.Properties
> import Exists.Ops
> import Util.VectExtensions1

> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Reachability

> %default total


We provide a default implementation for |reachable| that fulfill the
specifications required by "S1302_Reachability" on the basis of the
notion of predecessor. This can be formalized in terms of

> preds : X (S t) -> (n : Nat ** Vect n (X t))

Clients of this module are supposed to define |preds| as to be
compatible with |step| and |Y|. We express the compatibility conditions
in terms of

> eqeq : X t -> X t -> Bool

> -- eqeqSpec1 : (x : X t) -> so (eqeq x x)
> eqeqSpec1 : (x : X t) -> so (ReachabilityDefaults.eqeq x x)

> isIn : X t -> (n : Nat ** Vect n (X t)) -> Bool
> -- isIn {t} = VectExtensions1.isIn (X t) eqeq eqeqSpec1
> isIn {t} = VectExtensions1.isIn (X t) ReachabilityDefaults.eqeq ReachabilityDefaults.eqeqSpec1

> lemma3 : (x : X t) ->
>          (p : X t -> Bool) ->
>          (xs : (n : Nat ** Vect n (X t))) ->
>          so (p x) ->
>          -- so (x `isIn` xs) ->
>          so (x `ReachabilityDefaults.isIn` xs) ->
>          so (isAnyBy p xs)
> -- lemma3 {t} = VectExtensions1.lemma3 (X t) eqeq eqeqSpec1
> lemma3 {t} = VectExtensions1.lemma3 (X t) ReachabilityDefaults.eqeq ReachabilityDefaults.eqeqSpec1

> lemma6 : (p  : X t -> Bool) ->
>          (xs : (n : Nat ** Vect n (X t))) ->
>          so (isAnyBy p xs) ->
>          -- (x : X t ** (so (p x), so (x `isIn` xs)))
>          (x : X t ** (so (p x), so (x `ReachabilityDefaults.isIn` xs)))
> -- lemma6 {t} = VectExtensions1.lemma6 (X t) eqeq eqeqSpec1
> lemma6 {t} = VectExtensions1.lemma6 (X t) ReachabilityDefaults.eqeq ReachabilityDefaults.eqeqSpec1

These are:

> predsSpec1 : (x : X t) ->
>              (y : Y t x) ->
>              (x' : X (S t)) ->
>              so (x' `MisIn` step t x y) ->
>              -- so (x `isIn` (preds x'))
>              so (x `ReachabilityDefaults.isIn` (preds x'))

> predsSpec2 : (x' : X (S t)) ->
>              (x : X t) ->
>              -- so (x `isIn` (preds x')) ->
>              so (x `ReachabilityDefaults.isIn` (preds x')) ->
>              (y : Y t x ** so (x' `MisIn` step t x y))

If |preds| fulfill the above specifications a default definitions of
|reachable| can be given as follows:

> -- Reachability.reachable : X t -> Bool
> Reachability.reachable {t = Z} _ = True
> Reachability.reachable {t = S t} x' = isAnyBy reachable (preds x')

With the above definition we have:

> -- Reachability.reachableSpec0 : 
> --   (x : X Z) -> 
> --   so (reachable x)
> Reachability.reachableSpec0 x = oh

> -- Reachability.reachableSpec1 : 
> --   (x : X t) ->
> --   so (reachable x) ->
> --   (y : Y t x) ->
> --   (x' : X (S t)) ->
> --   so (x' `MisIn` (step t x y)) ->
> --   so (reachable x')
> Reachability.reachableSpec1 {t} x rx y x' x'ins = step4 where
>   -- step1 : so (x `isIn` (preds x'))
>   step1 : so (x `ReachabilityDefaults.isIn` (preds x'))
>   step1 = predsSpec1 x y x' x'ins
>   step2 : so (isAnyBy reachable (preds x'))
>   -- step2 = lemma3 x reachable (preds x') rx step1
>   step2 = ReachabilityDefaults.lemma3 x reachable (preds x') rx step1
>   step3 : isAnyBy reachable (preds x') = reachable x'
>   step3 = believe_me oh -- ?
>   step4 : so (reachable x')
>   step4 = leibniz (\ p => so p) step3 step2

> -- Reachability.reachableSpec2 : 
> --   (x' : X (S t)) -> 
> --   so (reachable x') ->
> --   (x : X t ** (y : Y t x ** (so (reachable x), so (x' `MisIn` (step t x y)))))
> Reachability.reachableSpec2 {t = t} x' rx' =
>   (x ** (y ** (xr, x'in))) where  
>     xrinpx' : (xx : X t ** (so (reachable xx), so (xx `isIn` (preds x'))))
>     -- xrinpx' : (xx : X t ** (so (reachable xx), so (xx `ReachabilityDefaults.isIn` (preds x'))))
>     xrinpx' = lemma6 reachable (preds x') rx'
>     -- xrinpx' = ReachabilityDefaults.lemma6 reachable (preds x') rx'
>     x  : X t
>     x  = outl xrinpx'
>     xr : so (reachable x)
>     xr = fst (outr xrinpx')
>     xinpx' : so (x `isIn` (preds x'))
>     -- xinpx' : so (x `ReachabilityDefaults.isIn` (preds x'))
>     xinpx' = snd (outr xrinpx')
>     -- yx'in : (yy : Y t x ** so (x' `MisIn` step t x yy))
>     yx'in : (y : Y t x ** so (x' `MisIn` step t x y))
>     yx'in = predsSpec2 x' x xinpx'
>     y : Y t x
>     y = outl yx'in
>     x'in : so (x' `MisIn` step t x y)
>     x'in = outr yx'in
