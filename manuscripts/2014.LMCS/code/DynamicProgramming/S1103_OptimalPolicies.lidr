> module OptimalPolicies

> import Data.Vect
> import Data.So

> import Logic.Properties
> import Fun.Ops
> import Rel.DecEq
> import Rel.ReflDecEq
> import Float.Properties
> import DynamicProgramming.S1101_Context
> import DynamicProgramming.S1102_OptimalControls

> %default total

> Policy : Type
> Policy = (x : State) -> Ctrl x

> PolicySeq : Nat -> Type
> PolicySeq n = Vect n Policy

> ctrl : (x : State) -> PolicySeq n -> CtrlSeq x n
> ctrl x Nil = Nil
> ctrl x (p :: ps) = (p x :: ctrl (step x (p x)) ps)

> modifyPolicySeq : (DecEq.DecEq State) => 
>                   PolicySeq n -> 
>                   CtrlSeq x n -> 
>                   PolicySeq n

> modifyPolicySeq {n = Z} Nil Nil = Nil

> modifyPolicySeq {n = S m} {x = x} (p :: ps) (y :: ys) = 
>    let ps' = modifyPolicySeq ps ys in
>      modifyDepFun p (x ** y) :: ps'

> modifyPolicySeqLemma : (ReflDecEq State) =>
>                        (ps : PolicySeq n) -> 
>                        (ys : CtrlSeq x n) ->
>                        ctrl x (modifyPolicySeq ps ys) = ys

> modifyPolicySeqLemma Nil Nil = Refl

> modifyPolicySeqLemma {x} {n = S m} (p :: ps) (y :: ys) = foo where
>   ps'  :  PolicySeq m
>   ps'  =  modifyPolicySeq ps ys
>   s1   :  ctrl (step x y) ps' = ys
>   s1   =  modifyPolicySeqLemma ps ys
>   p'   :  Policy 
>   p'   =  modifyDepFun p (x ** y)
>   s2   :  p' x = y
>   s2   =  modifyDepFunLemma p (x ** y)
>   s3   :  p' :: ps' = modifyPolicySeq (p :: ps) (y :: ys) -- = p' :: ps'
>   s3   =  Refl
>   s4   :  ctrl x (p' :: ps') = (p' x) :: ctrl (step x (p' x)) ps'
>   s4   =  Refl
>   s5   :  (p' x) :: ctrl (step x (p' x)) ps' = y :: ctrl (step x y) ps'
>   s5   =  replace  {a = Ctrl x}
>                    {x = p' x}
>                    {P = \ z => (p' x) :: ctrl (step x (p' x)) ps'  = 
>                                z      :: ctrl (step x z) ps'} s2 Refl
>   s6   :  y :: ctrl (step x y) ps' = y :: ys
>   -- s6   =  replace {a = CtrlSeq (step x y) m}
>   --                 {x = ctrl (step x y) ps'}
>   --                 {P = \ z => y :: ctrl (step x y) ps' = y :: z} s1 Refl
>   s6   =  rewrite s1 in Refl
>   s7   :  ctrl x (p' :: ps') = y :: ys   
>   s7   =  trans (trans s4 s5) s6
>   foo  :  ctrl x (modifyPolicySeq (p :: ps) (y :: ys)) = y :: ys
>   foo  =  replace  {a = PolicySeq (S m)}
>                    {x = p' :: ps'}
>                    {y = modifyPolicySeq (p :: ps) (y :: ys)}
>                    {P = \ z => ctrl x z = y :: ys} s3 s7

> val : (x : State) -> PolicySeq n -> Float
> val {n = Z}    _  _          =  0
> val {n = S m}  x  (p :: ps)  =  reward x (p x) x' + val x' ps where
>   x'  :  State  
>   x'  =  step x (p x)

> valueValLemma : (x : State) ->
>               (ps : PolicySeq n) -> 
>               val x ps = value (ctrl x ps)

> valueValLemma _ Nil = Refl

> valueValLemma x (p :: ps) = step4 where
>   y : Ctrl x
>   y = p x
>   x' : State
>   x' = step x y
>   ih : val x' ps = value (ctrl x' ps)
>   ih = valueValLemma x' ps
>   step1 : val x (p :: ps) = reward x y x' + val x' ps
>   step1 = Refl
>   step2 : val x (p :: ps) = reward x y x' + value (ctrl x' ps)
>   step2 = replace {P = \ z => val x (p :: ps) = reward x y x' + z} ih step1
>   -- a = b && x = y + a => x = y + b
>   step3 : reward x y x' + value (ctrl x' ps) = value (ctrl x (p :: ps))
>   step3 = Refl
>   step4 : val x (p :: ps) = value (ctrl x (p :: ps))
>   step4 = trans step2 step3

> valueValLemma' : (ps' : PolicySeq n) -> 
>                (ps : PolicySeq n) -> 
>                (x : State) ->
>                So (val x ps' <= val x ps) -> 
>                So (value (ctrl x ps') <= value (ctrl x ps))

> valueValLemma' ps' ps x o = l2 where
>    l1  : So (value (ctrl x ps') <= val x ps)
>    l1  = replace {P = \ z => So (z <= val x ps)} (valueValLemma x ps') o
>    l2  : So (value (ctrl x ps') <= value (ctrl x ps))
>    l2  = replace {P = \ z => So (value (ctrl x ps') <= z)} (valueValLemma x ps) l1

The notion of optimal sequence of policies:

> OptPolicySeq : (n : Nat) -> PolicySeq n -> Type
> OptPolicySeq n ps = (x : State) -> (ps' : PolicySeq n) -> So (val x ps' <= val x ps)

> nilIsOptPolicySeq : OptPolicySeq Z Nil
> nilIsOptPolicySeq x ps' = reflexive_Float_lte 0

> OptLemma : (ReflDecEq State) =>
>            (n : Nat) -> 
>            (ps : PolicySeq n) -> 
>            OptPolicySeq n ps ->
>            (x : State) ->
>            OptCtrlSeq (ctrl x ps)

> OptLemma n ps o x ys' = r  where
>    ps' : PolicySeq n
>    ps' = modifyPolicySeq ps ys'
>    m   : ctrl x ps' = ys'
>    m   = modifyPolicySeqLemma ps ys'
>    o'  : So (val x ps' <= val x ps)
>    o'  = o x ps'
>    l2  : So (value (ctrl x ps') <= value (ctrl x ps))
>    l2  = valueValLemma' ps' ps x o'
>    l3  : value (ctrl x ps') = value ys'
>    l3  = replace  {a = CtrlSeq x n}
>                   {x = ctrl x ps'}
>                   {y = ys'}
>                   {P = \z => value (ctrl x ps') = value z} m Refl
>    r   : So (value ys' <= value (ctrl x ps))
>    r   = replace {P = \ z => So (z <= value (ctrl x ps))} l3 l2


