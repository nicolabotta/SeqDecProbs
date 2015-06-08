> module BackwardsInduction

> import Data.So

> import Float.Postulates
> import Float.Properties
> import Logic.Properties

> import DynamicProgramming.S1101_Context
> import DynamicProgramming.S1102_OptimalControls
> import DynamicProgramming.S1103_OptimalPolicies
> import DynamicProgramming.S1104_MaxArgmax

> %default total


> valCtrl : (x : State) -> (ps : PolicySeq n) -> Ctrl x -> Float  
> valCtrl x ps y = reward x y x' + val x' ps where
>   x' : State
>   x' = step x y


If, for all |x : State| and for all |f : Ctrl x -> Float|, we are able to
select a control |y : Ctrl x| which maximises |f|, optimal sequences of
policies can be computed with Bellman's backwards induction algorithm.
This, in turns, follows from Bellman's optimality principle.

To express this principle, one needs the notion of optimal extension of
sequences of policies:

> OptExt : PolicySeq n -> Policy -> Type
> OptExt ps p = (p' : Policy) -> (x : State) -> So (val x (p' :: ps) <= val x (p :: ps))

Under the assumptions put forward in section MaxArgmax, it is easy to
compute optimal extensions for arbitrary sequences of policies:

> optExt : PolicySeq n -> Policy
> optExt ps x = argmax x (valCtrl x ps)-- where
> {-
>   f : Ctrl x -> Float  
>   f y = reward x y x' + val x' ps where
>     x' : State
>     x' = step x y
> -}

> OptExtLemma : (ps : PolicySeq n) -> OptExt ps (optExt ps)

To prove that |optExt ps| is indeed an optimal extension of |ps|
it is useful to recall:

val x (p' :: ps) 
  = {def. val, x' = step x (p' x)}
reward x (p' x) x' + val x' ps
  = {def. f}
f (p' x)
  <= {MaxSpec}
max x f
  = {ArgmaxSpec}
f (argmax x f)
  = {def. optExt}
f ((optExt ps) x)
  = {def. f, x' = step x (optExt ps x)}
reward x (optExt ps x) x' + val x' ps
  = {def. val}
val x ((optExt ps) :: ps)

which can also be formulated as

MaxSpec
  =>
f (p' x) <= max x f
  => {ArgmaxSpec}  
f (p' x) <= f (argmax f x)
  => {def. optExt ps}
f (p' x) <= f (optExt ps x)
  => {def. f, let x' = step x (p' x), x'' = step x (optExt ps x)}
reward x (p' x) x' + val x' ps 
<= 
reward x (optExt ps x) x'' + val x'' ps
  => {def. val}
val x (p' :: ps) <= val x ((optExt ps) :: ps)

> OptExtLemma ps p' x = step6 where
>   f : Ctrl x -> Float  
>   f = valCtrl x ps
>   step1 : So (f (p' x) <= max x f)  
>   step1 = maxSpec x f (p' x)
>   step2 : So (max x f == f (argmax x f))
>   step2 = symmetric_Float_eqeq (argmaxSpec x f)
>   step3 : So (max x f <= f (argmax x f))
>   step3 = sub_Float_eqeq_lte step2
>   step4 : So (f (p' x) <= f (argmax x f))
>   step4 = transitive_Float_lte step1 step3
>   step5 : argmax x f = (optExt ps) x
>   step5 = believe_me Oh
>   step6 : So (f (p' x) <= f ((optExt ps) x))
>   step6 = replace {P = \ a => So (f (p' x) <= f a)} step5 step4

Now Bellman's principle of optimality states that optimal policy
sequences  extended with optimal extensions are themselves optimal:

> Bellman  :  (ps : PolicySeq n) -> OptPolicySeq n ps ->
>             (p : Policy) -> OptExt ps p ->
>             OptPolicySeq (S n) (p :: ps)

The principle can be easily proved. One has

val x (p' :: ps')
  = {def. of val, let x' = step x (p' x)}  
reward x (p' x) x' + val x' ps'
  <= {OptPolicySeq ps, monotonicity of +}
reward x (p' x) x' + val x' ps
  = {def. of val}  
val x (p' :: ps)
  <= {OptExt ps p}
val x (p :: ps) 

or, equivalently:

val x (p' :: ps')
  <= {def. of val, OptPolicySeq ps, monotonicity of +}
val x (p' :: ps)
  and
val x (p' :: ps)
  <= {OptExt ps p}
val x (p :: ps) 
  -> {transitivity of <=}
val x (p' :: ps') <= val x (p :: ps) 

and a proof of Bellman's principle can be constructed as follows:

> Bellman {n} ps ops p oep = opps where
>   %assert_total
>   opps : OptPolicySeq (S n) (p :: ps)
>   opps x (p' :: ps') = transitive_Float_lte step2 step3 where
>     step1 : So (val (step x (p' x)) ps' <= val (step x (p' x)) ps)
>     step1 = ops (step x (p' x)) ps'
>     step2 : So (val x (p' :: ps') <= val x (p' :: ps))
>     step2 = monotone_Float_plus_lte (reward x (p' x) (step x (p' x))) step1
>     step3 : So (val x (p' :: ps) <= val x (p :: ps))
>     step3 = oep p' x

Bellman's principle suggests that the problem of computing an optimal
sequance of policies of length n (and thus, thank to OptLemma, optimal
sequences of controls of the same length) can be solved by computing n
optimal extensions by backwards induction. The following implementation
and lemma shows that this is in fact the case:

> backwardsInduction        :  (n : Nat) -> PolicySeq n
> backwardsInduction Z      =  Nil
> backwardsInduction (S n)  =  (optExt ps) :: ps where
>   ps : PolicySeq n
>   ps = backwardsInduction n

> BackwardsInductionLemma : (n : Nat) -> OptPolicySeq n (backwardsInduction n)
> BackwardsInductionLemma Z = nilIsOptPolicySeq
> BackwardsInductionLemma (S m) = 
>   Bellman ps ops p oep where
>     ps : PolicySeq m
>     ps = backwardsInduction m
>     ops : OptPolicySeq m ps
>     ops =  BackwardsInductionLemma m
>     p : Policy
>     p = optExt ps
>     oep : OptExt ps p
>     oep = OptExtLemma ps

