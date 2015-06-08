> module ViabilityDefaults

> import Data.So

> import Logic.Properties
> import Exists.Ops
> import Util.VectExtensions1

> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Viability

> %default total


We provide a default implementation for |viable| that fulfill the
specifications required by "S1302_Viability" on the basis of the
notion of successor. This can be formalized in terms of

> succs : X t -> (n : Nat ** Vect n (M (X (S t))))

Clients of this module are supposed to define |succs| as to be
compatible with |step| and |Y|. We express the compatibility conditions
in terms of

> eqeq : M (X t) -> M (X t) -> Bool

> eqeqSpec1 : (x : M (X t)) -> So (eqeq x x)

> isIn : M (X t) -> (n : Nat ** Vect n (M (X t))) -> Bool
> isIn {t} = VectExtensions1.isIn (M (X t)) eqeq eqeqSpec1

> lemma2 : (mxs : (n : Nat ** Vect n (M (X t)))) ->
>          So (not (isEmpty mxs)) ->
>          (mx : M (X t) ** So (mx `isIn` mxs))
> lemma2 {t} = VectExtensions1.lemma2 (M (X t)) eqeq eqeqSpec1

> lemma3 : (mx : M (X t)) ->
>          (p : M (X t) -> Bool) ->
>          (mxs : (n : Nat ** Vect n (M (X t)))) ->
>          So (p mx) ->
>          So (mx `isIn` mxs) ->
>          So (isAnyBy p mxs)
> lemma3 {t} = VectExtensions1.lemma3 (M (X t)) eqeq eqeqSpec1

> lemma6 : (p  : M (X t) -> Bool) ->
>          (mxs : (n : Nat ** Vect n (M (X t)))) ->
>          So (isAnyBy p mxs) ->
>          (mx : M (X t) ** (So (p mx), So (mx `isIn` mxs)))
> lemma6 {t} = VectExtensions1.lemma6 (M (X t)) eqeq eqeqSpec1

These are:

> succsSpec1  :  (x : X t) ->
>                (y : Y t x) ->
>                So ((step t x y) `isIn` (succs x))
> succsSpec2  :  (x : X t) ->
>                (mx' : M (X (S t))) ->
>                So (mx' `isIn` (succs x)) ->
>                (y : Y t x ** mx' = step t x y)

If |succs| fulfill the above specifications a default definitions of
|viable| can be given as follows:

> -- Viability.viable : (n : Nat) -> X t -> Bool
> Viability.viable Z _ = True
> Viability.viable (S n) x = isAnyBy (\ mx => MareAllTrue (Mmap (viable n) mx)) (succs x)
> -- Viability.viable {t = t} (S n) x =
>   -- isAnyBy (\ mx => MareAllTrue (Mmap (viable {t = S t} n) mx)) (succs x)

With the above definition we have:

> -- Viability.viableSpec0 : 
> --   (x : X t) -> 
> --   So (viable Z x)
> Viability.viableSpec0 x = Oh

> -- Viability.viableSpec1 : 
> --   (x : X t) -> 
> --   So (viable (S n) x) -> 
> --   -- (y : Y t x ** So (x' `MisIn` (step t x y)) -> So (viable {t = S t} n x'))
> --   (y : Y t x ** So (MareAllTrue (Mmap (viable {t = S t} n) (step t x y))))
> Viability.viableSpec1 {t} {n} x v = s11 where
>   s1 : So (isAnyBy (\ mx => MareAllTrue (Mmap (viable {t = S t} n) mx)) (succs x))
>   s1 = v
>   s2 : (mx' : M (X (S t)) **
>         (So (MareAllTrue (Mmap (viable {t = S t} n) mx')),
>          So (isIn {t = S t} mx' (succs x))
>         )
>        )
>   s2 = lemma6 {t = S t} (\ mx => MareAllTrue (Mmap (viable {t = S t} n) mx)) (succs x) s1
>   s3 : M (X (S t))
>   s3 = outl s2
>   s4 : So (isIn {t = S t} s3 (succs x))
>   s4 = snd (outr s2)
>   s5 : (yy : Y t x ** s3 = step t x yy)
>   s5 = succsSpec2 x s3 s4
>   s6 : Y t x
>   s6 = outl s5
>   s7 : So (MareAllTrue (Mmap (viable {t = S t} n) s3))
>   s7 = fst (outr s2)
>   s8 : s3 = step t x s6
>   s8 = outr s5
>   s9 : So (MareAllTrue (Mmap (viable {t = S t} n) (step t x s6)))
>   s9 = leibniz (\ xSt => So (MareAllTrue (Mmap (viable {t = S t} n) xSt))) s8 s7
>   s11 : (yy : Y t x ** 
>          So (MareAllTrue (Mmap (viable {t = S t} n) (step t x yy))))
>   s11 = (s6 ** s9)

> -- Viability.viableSpec2 : 
> --   (x : X t) -> 
> --   -- (y : Y t x ** So (x' `MisIn` (step t x y)) -> So (viable {t = S t} n x')) -> 
> --   (y : Y t x ** So (MareAllTrue (Mmap (viable {t = S t} n) (step t x y)))) ->
> --   So (viable (S n) x)
> Viability.viableSpec2 {t} {n} x yv = step5 where
>   y : Y t x
>   y = outl yv
>   mx' : M (X (S t))
>   mx' = step t x y
>   p : M (X (S t)) -> Bool
>   -- p = \ mx => MareAllTrue (Mmap (viable {t = S t} n) mx)
>   p = \ mx' => MareAllTrue (Mmap (viable {t = S t} n) mx')
>   pmx' : So (MareAllTrue (Mmap (viable {t = S t} n) mx'))
>   pmx' = outr yv
>   mxs' : (n : Nat ** Vect n (M (X (S t))))
>   mxs' = succs x
>   mx'isInmxs' : So (isIn {t = S t} mx' mxs')
>   mx'isInmxs' = succsSpec1 x y
>   step4 : So (isAnyBy  (\ mx => MareAllTrue (Mmap (viable {t = S t} n) mx)) mxs')
>   step4 = lemma3 {t = S t} mx' p (succs x) pmx' mx'isInmxs'
>   step5 : So (viable (S n) x)
>   step5 = step4
