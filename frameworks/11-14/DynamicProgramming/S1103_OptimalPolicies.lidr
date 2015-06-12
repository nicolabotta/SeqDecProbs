> module OptimalPolicies

> import Data.Vect
> import Data.So

> import Logic.Properties
> -- import Logic.Ops
> import Fun.Ops
> import Rel.DecEq
> import Rel.ReflDecEq
> import Float.Properties
> import DynamicProgramming.S1101_Context
> import DynamicProgramming.S1102_OptimalControls

> %default total

It is easy to compute sequences of feasible controls if one has a rule
that tells one which (feasible) control to select when in a given
state. Such rules are called policies

> Policy : Type
> Policy = (x : X) -> Y x

Sequences of policies of length n can be represented by values of
type |Vect Policy n|: 

> PolicySeq : Nat -> Type
> PolicySeq n = Vect n Policy

Given one such sequences, the corresponding sequence of controls is

> %assert_total
> ctrl : (x : X) -> PolicySeq n -> CtrlSeq x n
> ctrl x Nil = Nil
> ctrl x (p :: ps) = (p x :: ctrl (step x (p x)) ps)

If |X| is in |ReflDecEq|, given a sequence of policies |ps| and a
sequence of controls |ys| of the same length, one can construct a new
policy sequence |ps'| whose corresponding controls are |ys|. This
construction is crucial for proving that sequences of controls obtained
from optimal policy sequences are optimal, see below.

> %assert_total
> modifyPolicySeq : (DecEq.DecEq X) => 
>                   PolicySeq n -> 
>                   CtrlSeq x n -> 
>                   PolicySeq n

> modifyPolicySeq {n = Z} Nil Nil = Nil

> modifyPolicySeq {n = S m} {x = x} (p :: ps) (y :: ys) = 
>    let ps' = modifyPolicySeq ps ys in
>      modifyDepFun p (x ** y) :: ps'

> %assert_total
> modifyPolicySeqLemma : (ReflDecEq X) =>
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
>   s5   =  replace  {a = Y x}
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

The value (in terms of cumulated rewards) of a sequence of policies is
given by: 

> %assert_total
> Val : (x : X) -> PolicySeq n -> Float
> Val {n = Z} _ _ = 0
> Val {n = S m} x (p :: ps) = reward x (p x) x' + Val x' ps where
>   x' : X  
>   x' = step x (p x)

It is easy to prove 

Val x ps = val (ctrl x ps)

Base case: 
  Val x Nil = val (ctrl x Nil)

  Val x Nil
    = {- def. of Val -}
  0
    = {- def. of val -}
  val Nil
    = {- def. of ctrl -}
  val (ctrl x Nil)

Induction step: 
  Val x ps = val (ctrl x ps) 
    => 
  Val x (p :: ps) = val (ctrl x (p :: ps))

  Val x (p :: ps)
    = {- def. of Val with y = p x, x' = step x y -}
  reward x y x' + Val x' ps
    = {- induction hypothesis -}
  reward x y x' + val (ctrl x' ps)
    = {- def. of val -}
  val (y :: (ctrl x' ps))
    = {- def. of y, x', ctrl -}
  val (ctrl x (p :: ps))

We can implement the proof in Idris and (type) check its correctness:

> %assert_total
> valValLemma : (x : X) ->
>               (ps : PolicySeq n) -> 
>               Val x ps = val (ctrl x ps)

> valValLemma _ Nil = Refl

> valValLemma x (p :: ps) = step4 where
>   y : Y x
>   y = p x
>   x' : X
>   x' = step x y
>   ih : Val x' ps = val (ctrl x' ps)
>   ih = valValLemma x' ps
>   step1 : Val x (p :: ps) = reward x y x' + Val x' ps
>   step1 = Refl
>   step2 : Val x (p :: ps) = reward x y x' + val (ctrl x' ps)
>   step2 = replace {P = \ z => Val x (p :: ps) = reward x y x' + z} ih step1
>   -- a = b && x = y + a => x = y + b
>   step3 : reward x y x' + val (ctrl x' ps) = val (ctrl x (p :: ps))
>   step3 = Refl
>   step4 : Val x (p :: ps) = val (ctrl x (p :: ps))
>   step4 = trans step2 step3

> valValLemma' : (ps' : PolicySeq n) -> 
>                (ps : PolicySeq n) -> 
>                (x : X) ->
>                So (Val x ps' <= Val x ps) -> 
>                So (val (ctrl x ps') <= val (ctrl x ps))

> valValLemma' ps' ps x o = l2 where
>    l1  : So (val (ctrl x ps') <= Val x ps)
>    l1  = replace {P = \ z => So (z <= Val x ps)} (valValLemma x ps') o
>    l2  : So (val (ctrl x ps') <= val (ctrl x ps))
>    l2  = replace {P = \ z => So (val (ctrl x ps') <= z)} (valValLemma x ps) l1

The notion of optimal sequence of policies:

> OptPolicySeq : (n : Nat) -> PolicySeq n -> Type
> OptPolicySeq n ps = (x : X) -> 
>                     (ps' : PolicySeq n) -> 
>                     So (Val x ps' <= Val x ps)

(Sanity check: Nil is optimal

> nilIsOptPolicySeq : OptPolicySeq Z Nil
> nilIsOptPolicySeq x ps' = reflexive_Float_lte 0

) is interesting because of the following lemma:

> OptLemma : (ReflDecEq X) =>
>            (n : Nat) -> 
>            (ps : PolicySeq n) -> 
>            OptPolicySeq n ps ->
>            (x : X) ->
>            OptCtrlSeq (ctrl x ps)

> OptLemma n ps o x ys' = r  where
  
1. construct ps' s.t. ctrl x ps' = ys'

>    ps' : PolicySeq n
>    ps' = modifyPolicySeq ps ys'
>    m   : ctrl x ps' = ys'
>    m   = modifyPolicySeqLemma ps ys'

2. apply o to deduce Val x ps' <= Val x ps

>    o'  : So (Val x ps' <= Val x ps)
>    o'  = o x ps'
>    l2  : So (val (ctrl x ps') <= val (ctrl x ps))
>    l2  = valValLemma' ps' ps x o'

3. conclude by applying valVal that val ys' <= val (ctrl x ps)

>    l3  : val (ctrl x ps') = val ys'
>    l3  = replace  {a = CtrlSeq x n}
>                   {x = ctrl x ps'}
>                   {y = ys'}
>                   {P = \z => val (ctrl x ps') = val z} m Refl
>    r   : So (val ys' <= val (ctrl x ps))
>    r   = replace {P = \ z => So (z <= val (ctrl x ps))} l3 l2

|OptLemma| ensures that optimal control sequences can be computed from
optimal sequences of policies. This is particularly useful because, as
we will see in 'S1105', optimal sequences of policies can be computed
efficiently via Bellman's backwards induction algorithm.

