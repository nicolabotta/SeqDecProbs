> module BackwardsInduction


> import Float.Postulates
> import Float.Properties
> import Logic.Properties
> import DynamicProgramming.S1101_Context
> import DynamicProgramming.S1102_OptimalControls
> import DynamicProgramming.S1103_OptimalPolicies
> import DynamicProgramming.S1104_MaxArgmax

> %default total


> valY : (x : X) -> (ps : PolicySeq n) -> Y x -> Float  
> valY x ps y = reward x y x' + Val x' ps where
>   x' : X
>   x' = step x y


If, for all |x : X| and for all |f : Y x -> Float|, we are able to
select a control |y : Y x| which maximises |f|, optimal sequences of
policies can be computed with Bellman's backwards induction algorithm.
This, in turns, follows from Bellman's optimality principle.

To express this principle, one needs the notion of optimal extension of
sequences of policies:

> OptExt : PolicySeq n -> Policy -> Type
> OptExt ps p  =  (p' : Policy) ->
>                 (x : X) ->
>                 so (Val x (p' :: ps) <= Val x (p :: ps))

Under the assumptions put forward in section MaxArgmax, it is easy to
compute optimal extensions for arbitrary sequences of policies:

> optExt : PolicySeq n -> Policy
> optExt ps x = argmax x (valY x ps)-- where
> {-
>   f : Y x -> Float  
>   f y = reward x y x' + Val x' ps where
>     x' : X
>     x' = step x y
> -}

> OptExtLemma : (ps : PolicySeq n) -> OptExt ps (optExt ps)

To prove that |optExt ps| is indeed an optimal extension of |ps|
it is useful to recall:

Val x (p' :: ps) 
  = {def. Val, x' = step x (p' x)}
reward x (p' x) x' + Val x' ps
  = {def. f}
f (p' x)
  <= {MaxSpec}
max x f
  = {ArgmaxSpec}
f (argmax x f)
  = {def. optExt}
f ((optExt ps) x)
  = {def. f, x' = step x (optExt ps x)}
reward x (optExt ps x) x' + Val x' ps
  = {def. Val}
Val x ((optExt ps) :: ps)

which can also be formulated as

MaxSpec
  =>
f (p' x) <= max x f
  => {ArgmaxSpec}  
f (p' x) <= f (argmax f x)
  => {def. optExt ps}
f (p' x) <= f (optExt ps x)
  => {def. f, let x' = step x (p' x), x'' = step x (optExt ps x)}
reward x (p' x) x' + Val x' ps 
<= 
reward x (optExt ps x) x'' + Val x'' ps
  => {def. Val}
Val x (p' :: ps) <= Val x ((optExt ps) :: ps)

> OptExtLemma ps p' x = step6 where
>   f : Y x -> Float  
>   f = valY x ps
>   step1 : so (f (p' x) <= max x f)  
>   step1 = maxSpec x f (p' x)
>   step2 : so (max x f == f (argmax x f))
>   step2 = symmetric_Float_eqeq {a1 = f (argmax x f)} 
>                                {a2 = max x f} 
>                                (argmaxSpec x f)
>   step3 : so (max x f <= f (argmax x f))
>   step3 = sub_Float_eqeq_lte {a1 = max x f} 
>                              {a2 = f (argmax x f)} 
>                              step2
>   step4 : so (f (p' x) <= f (argmax x f))
>   step4 = transitive_Float_lte {a1 = f (p' x)} 
>                                {a2 = max x f}            
>                                {a3 = f (argmax x f)}
>                                step1 
>                                step3
>   step5 : argmax x f = (optExt ps) x
>   step5 = believe_me oh
>   step6 : so (f (p' x) <= f ((optExt ps) x))
>   step6 = replace {P = \ a => so (f (p' x) <= f a)} step5 step4

Now Bellman's principle of optimality states that optimal policy
sequences  extended with optimal extensions are themselves optimal:

> Bellman  :  (ps : PolicySeq n) ->
>             OptPolicySeq n ps ->
>             (p : Policy) ->
>             OptExt ps p ->
>             OptPolicySeq (S n) (p :: ps)

The principle can be easily proved. One has

Val x (p' :: ps')
  = {def. of Val, let x' = step x (p' x)}  
reward x (p' x) x' + Val x' ps'
  <= {OptPolicySeq ps, monotonicity of +}
reward x (p' x) x' + Val x' ps
  = {def. of Val}  
Val x (p' :: ps)
  <= {OptExt ps p}
Val x (p :: ps) 

or, equivalently:

Val x (p' :: ps')
  <= {def. of Val, OptPolicySeq ps, monotonicity of +}
Val x (p' :: ps)
  and
Val x (p' :: ps)
  <= {OptExt ps p}
Val x (p :: ps) 
  -> {transitivity of <=}
Val x (p' :: ps') <= Val x (p :: ps) 

and a proof of Bellman's principle can be constructed as follows:

> Bellman {n} ps ops p oep = opps where
>   %assert_total
>   opps : OptPolicySeq (S n) (p :: ps)
>   opps x (p' :: ps') = transitive_Float_lte 
>                        {a1 = Val x (p' :: ps')}
>                        {a2 = Val x (p' :: ps)}
>                        {a3 = Val x (p :: ps)}
>                        step2 
>                        step3 where
>     step1 : so (Val (step x (p' x)) ps' <= Val (step x (p' x)) ps)
>     step1 = ops (step x (p' x)) ps'
>     step2 : so (Val x (p' :: ps') <= Val x (p' :: ps))
>     step2 = monotone_Float_plus_lte {a1 = Val (step x (p' x)) ps'}
>                                     {a2 = Val (step x (p' x)) ps}
>                                     (reward x (p' x) 
>                                     (step x (p' x))) 
>                                     step1
>     step3 : so (Val x (p' :: ps) <= Val x (p :: ps))
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

> BackwardsInductionLemma : (n : Nat) -> 
>                           OptPolicySeq n (backwardsInduction n)
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

