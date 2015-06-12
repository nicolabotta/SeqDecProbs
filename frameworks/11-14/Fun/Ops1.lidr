> module Ops1

> import Eq.Properties
> import DecEq.Properties

> %default total


> modifyFun' : (f : alpha -> beta) -> 
>              (a : alpha) -> 
>              (b : beta) ->
>              (a' : alpha) ->
>              (Dec (a = a')) ->
>              beta
> modifyFun' _ _ b _ (Yes _) = b
> modifyFun' f _ _ a' (No _) = f a'
                               

> modifyFun : (DecEq alpha) => 
>             (f: alpha -> beta) -> 
>             (a : alpha) -> 
>             (b : beta) -> 
>             (alpha -> beta)
> modifyFun f a b a' = modifyFun' f a b a' (decEq a a')


> modifyFunSpec1 : (DecEq alpha) => 
>                  (f  : alpha -> beta) ->
>                  (a  : alpha) ->
>                  (b  : beta) ->
>                  (a' : alpha) ->
>                  (p  : a = a') ->  
>                  (modifyFun f a b) a' = b
> modifyFunSpec1 f a b a' p with (decEqLemma1 a a')
>   | (Left l) = s5 where 
>     p' : a = a'
>     p' = getWitness l
>     s1 : decEq a a' = Yes p'
>     s1 = getProof l
>     s2 : modifyFun f a b a' = modifyFun' f a b a' (decEq a a')
>     s2 = refl
>     s3 : modifyFun' f a b a' (decEq a a') = modifyFun' f a b a' (Yes p')
>     s3 = cong {a = decEq a a'}
>               {b = Yes p'}
>               {f = \ x => modifyFun' f a b a' x}
>               s1
>     s4 : modifyFun' f a b a' (Yes p') = b
>     s4 = refl
>     s5 : modifyFun f a b a' = b
>     s5 = trans (trans s2 s3) s4
>   | (Right r) = FalseElim ((getWitness r) p)

> modifyFunSpec2 : (DecEq alpha) => 
>                  (f  : alpha -> beta) ->
>                  (a  : alpha) ->
>                  (b  : beta) ->
>                  (a' : alpha) ->
>                  (p  : Not (a = a')) ->
>                  (modifyFun f a b) a' = f a'
> modifyFunSpec2 f a b a' p with (decEqLemma1 a a')
>   | (Left l) = FalseElim (p (getWitness l))
>   | (Right r) = s5 where 
>     p' : Not (a = a')
>     p' = getWitness r
>     s1 : decEq a a' = No p'
>     s1 = getProof r
>     s2 : modifyFun f a b a' = modifyFun' f a b a' (decEq a a')
>     s2 = refl
>     s3 : modifyFun' f a b a' (decEq a a') = modifyFun' f a b a' (No p')
>     s3 = cong {a = decEq a a'}
>               {b = No p'}
>               {f = \ x => modifyFun' f a b a' x}
>               s1
>     s4 : modifyFun' f a b a' (No p') = f a'
>     s4 = refl
>     s5 : modifyFun f a b a' = f a'
>     s5 = trans (trans s2 s3) s4


> modifyFunLemma1 : (DecEq alpha) => 
>                   (f  : alpha -> beta) ->
>                   (a  : alpha) ->
>                   (b  : beta) ->
>                   (modifyFun f a b) a = b
> modifyFunLemma1 f a b = modifyFunSpec1 f a b a refl


> modifyFunLemma2 : (DecEq alpha) => 
>                   (f  : alpha -> beta) ->
>                   (a  : alpha) ->
>                   modifyFun f a (f a) = f


> modifyDepFun' : (f : (a : alpha) -> beta a) -> 
>                 (a : alpha) -> 
>                 (b : beta a) ->
>                 (a' : alpha) ->
>                 (Dec (a = a')) ->
>                 beta a'
> modifyDepFun' _ _ b _ (Yes p) = replace p b
> modifyDepFun' f _ _ a' (No _) = f a'


> modifyDepFun : (DecEq alpha) => 
>                (f : (a : alpha) -> beta a) -> 
>                (a : alpha) -> 
>                (b : beta a) -> 
>                ((a : alpha) -> beta a)
> modifyDepFun f a b a' = modifyDepFun' f a b a' (decEq a a')


> modifyDepFunSpec1 : (DecEq alpha) => 
>                     (f  : (a : alpha) -> beta a) ->
>                     (a  : alpha) ->
>                     (b  : beta a) ->
>                     (a' : alpha) ->
>                     (p  : a = a') ->  
>                     (p' : a = a' ** (modifyDepFun f a b) a' = replace p' b)
> modifyDepFunSpec1 f a b a' p with (decEqLemma1 a a')
>   | (Left l) = (p' ** s5) where 
>     p' : a = a'
>     p' = getWitness l
>     s1 : decEq a a' = Yes p'
>     s1 = getProof l
>     s2 : modifyDepFun f a b a' = modifyDepFun' f a b a' (decEq a a')
>     s2 = refl
>     s3 : modifyDepFun' f a b a' (decEq a a') = modifyDepFun' f a b a' (Yes p')
>     s3 = cong {a = decEq a a'}
>               {b = Yes p'}
>               {f = \ x => modifyDepFun' f a b a' x}
>               s1
>     s4 : modifyDepFun' f a b a' (Yes p') = replace p' b
>     s4 = refl
>     s5 : modifyDepFun f a b a' = replace p' b
>     s5 = trans (trans s2 s3) s4
>   | (Right r) = FalseElim ((getWitness r) p)


> modifyDepFunSpec2 : (DecEq alpha) => 
>                     (f  : (a : alpha) -> beta a) ->
>                     (a  : alpha) ->
>                     (b  : beta a) ->
>                     (a' : alpha) ->
>                     (p  : Not (a = a')) ->  
>                     (modifyDepFun f a b) a' = f a'
> modifyDepFunSpec2 f a b a' p with (decEqLemma1 a a')
>   | (Left l) = FalseElim (p (getWitness l))
>   | (Right r) = s5 where 
>     p' : Not (a = a')
>     p' = getWitness r
>     s1 : decEq a a' = No p'
>     s1 = getProof r
>     s2 : modifyDepFun f a b a' = modifyDepFun' f a b a' (decEq a a')
>     s2 = refl
>     s3 : modifyDepFun' f a b a' (decEq a a') = modifyDepFun' f a b a' (No p')
>     s3 = cong {a = decEq a a'}
>               {b = No p'}
>               {f = \ x => modifyDepFun' f a b a' x}
>               s1
>     s4 : modifyDepFun' f a b a' (No p') = f a'
>     s4 = refl
>     s5 : modifyDepFun f a b a' = f a'
>     s5 = trans (trans s2 s3) s4


> modifyDepFunLemma1 : (DecEq alpha) => 
>                      (f  : (a : alpha) -> beta a) ->
>                      (a  : alpha) ->
>                      (b  : beta a) ->
>                      (modifyDepFun f a b) a = b
> modifyDepFunLemma1 {alpha} {beta} f a b = s2 where
>   s0 : (p : a = a ** (modifyDepFun f a b) a = replace p b)
>   s0 = modifyDepFunSpec1 f a b a refl
>   p : a = a
>   p = getWitness s0
>   s1 : (modifyDepFun f a b) a = replace {x = a} {y = a} {P = beta} p b
>   s1 = getProof s0
>   s2 : (modifyDepFun f a b) a = b
>   s2 = replace {x = replace p b}
>                {y = b}
>                {P = \ z => (modifyDepFun f a b) a = z}
>                (eqLemma1 a b p)
>                s1

