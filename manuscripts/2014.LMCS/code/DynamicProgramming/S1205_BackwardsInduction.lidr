> module BackwardsInduction


> import Exists.Ops

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability
> import DynamicProgramming.S1203_OptimalPolicies
> import DynamicProgramming.S1204_MaxArgmax


> %default total


> depPairId : {X : Type, P : X -> Type} ->
>             (dep_pair : (x : X ** P x)) -> 
>             dep_pair = (outl dep_pair ** getProof dep_pair)
> depPairId (x ** y) = refl

If, for all reachable and viable |x : X t| and for all |f : (y : Y t x
** so (viable n (step t x y))) -> Float|, we are able to select a
control which maximises |f|, optimal sequences of policies can be
computed with Bellman's backwards induction algorithm. This, in turn,
follows from Bellman's optimality principle.

To express this principle, one needs the notion of optimal extension of
sequences of policies:

> OptExtension : (t : Nat) -> 
>                (n : Nat) -> 
>                PolicySeq (S t) n -> 
>                Policy t (S n) -> 
>                Type

> OptExtension t n ps p =  
>   (p' : Policy t (S n)) ->
>   (x : X t) ->
>   (r : so (reachable x)) -> 
>   (v : so (viable (S n) x)) -> 
>   so (Val t (S n) x r v (p' :: ps) <= Val t (S n) x r v (p :: ps))


Under the assumptions put forward in S1204_MaxArgmax.lidr, it is easy to
compute optimal extensions for arbitrary sequences of policies:

> optExtension : (t : Nat) -> 
>                (n : Nat) -> 
>                PolicySeq (S t) n -> 
>                Policy t (S n)

> optExtension t n ps = p where
>   p : Policy t (S n)
>   p x r v = yq where 
>     yq : (y : Y t x ** so (viable {t = S t} n (step t x y)))
>     yq = argmax n x r v f where
>       f : (y : Y t x ** so (viable {t = S t} n (step t x y))) -> Float  
>       f (y ** v') = reward t x y x' + Val (S t) n x' r' v' ps where
>         x' : X (S t)
>         x' = step t x y
>         r' : so (reachable {t = S t} x')
>         r' = reachableSpec1 x r y


> OptExtensionLemma : 
>   (t : Nat) -> 
>   (n : Nat) -> 
>   (ps : PolicySeq (S t) n) ->
>   OptExtension t n ps (optExtension t n ps)


To prove that |optExtension t n ps| is indeed an optimal extension of |ps|
it is useful to recall:

Val t (S n) x r v (p' :: ps) 
  = {def. Val, 
     y  = outl (p' x r v)
     x' = step t x y
     r' = reachability1 x r y
     v' = outr (p' x r v)
    }
reward t x y x' + Val (S t) n x' r' v' ps
  = {def. f}
f (p' x r v)
  <= {MaxSpec}
max n x r v f
  = {ArgmaxSpec}
f (argmax n x r v f)
  = {def. optExtension}
f ((optExtension t n ps) x r v)
  = {def. f, 
     oy  = outl (optExtension t n ps x r v),
     ox' = step t x oy,
     or' = reachability1 x r oy,
     ov' = outr (optExtension t n ps x r v)
    }
reward t x oy ox' + Val (S t) n ox' or' ov' ps
  = {def. Val}
Val t (S n) x r v ((optExtension t n ps) :: ps)

which can also be formulated as

MaxSpec
  =>
f (p' x r v) <= max n x r v f
  => {ArgmaxSpec}  
f (p' x r v) <= f (argmax n x r v f)
  => {def. optExtension ps}
f (p' x r v) <= f (optExtension t n ps x r v)
  => {def. f, 
      y  = outl (p' x r v),
      x' = step t x y,
      r' = reachability1 x r y,
      v' = outr (p' x r v), 
      oy  = outl (optExtension t n ps x r v),
      ox' = step t x oy,
      or' = reachability1 x r oy,
      ov' = outr (optExtension t n ps x r v)  
     }
reward t x y x' + Val (S t) n x' r' v' ps 
<= 
reward t x oy ox' + Val (S t) n ox' or' ov' ps
  => {def. Val}
Val t (S n) x r v (p' :: ps) <= Val t (S n) x r v ((optExtension t n ps) :: ps)

> OptExtensionLemma t n ps p' x r v = step6 where
>   f : (y : Y t x ** so (viable {t = S t} n (step t x y))) -> Float  
>   f (y ** v') = reward t x y x' + Val (S t) n x' r' v' ps where
>     x' : X (S t)
>     x' = step t x y
>     r' : so (reachable {t = S t} x')
>     r' = reachableSpec1 x r y
>   step1 : so (f (p' x r v) <= max n x r v f)  
>   step1 = maxSpec n x r v f (p' x r v)
>   step2 : so (max n x r v f == f (argmax n x r v f))
>   step2 = symmetric_Float_eqeq {a1 = f (argmax n x r v f)} 
>                                {a2 = max n x r v f} 
>                                (argmaxSpec n x r v f)
>   step3 : so (max n x r v f <= f (argmax n x r v f))
>   step3 = sub_Float_eqeq_lte {a1 = max n x r v f} {a2 = f (argmax n x r v f)} step2
>   step4 : so (f (p' x r v) <= f (argmax n x r v f))
>   step4 = transitive_Float_lte {a1 = f (p' x r v)} 
>                                {a2 = max n x r v f} 
>                                {a3 = f (argmax n x r v f)} step1 step3
>   step4'' : argmax n x r v f = argmax n x r v f 
>   step4'' = refl
>   step4' : argmax n x r v f = (optExtension t n ps) x r v
>   step4' = believe_me step4''
>   step5 : so (f (p' x r v) <= f ((optExtension t n ps) x r v))
>   step5 = leibniz (\ a => so (f (p' x r v) <= f a)) step4' step4
>   y1 : Y t x
>   y1 = outl (p' x r v)
>   x1' : X (S t)
>   x1' = step t x y1
>   r1' : so (reachable {t = S t} x1')
>   r1' = reachableSpec1 x r y1
>   v1' : so (viable {t = S t} n x1')
>   v1' = outr (p' x r v)
>   oy : Y t x
>   oy = outl ((optExtension t n ps) x r v)
>   ox' : X (S t)
>   ox' = step t x oy
>   or' : so (reachable {t = S t} ox')
>   or' = reachableSpec1 x r oy
>   ov' : so (viable {t = S t} n ox')
>   ov' = outr ((optExtension t n ps) x r v)
>   step1234 : p' x r v = 
>               Sg_intro 
>               {P = \ fresh_y  => 
>                      so (viable {t = S t} n (step t x fresh_y))}
>               y1 v1' 
>   step1234 = depPairId (p' x r v)

>   step122 : f (p' x r v) = reward t x y1 x1' + 
>                            Val (S t) n x1' r1' v1' ps
>   step122 = cong {f = f} step1234 
>   
>   step120 : optExtension t n ps x r v =
>               Sg_intro 
>               {P = \ fresh_y  => 
>                      so (viable {t = S t} n (step t x fresh_y))}
>               oy ov'
>   step120 = depPairId (optExtension t n ps x r v)
>   step121 : f (optExtension t n ps x r v) =
>             reward t x oy ox' + Val (S t) n ox' or' ov' ps
>   step121 = cong {f = f} step120
>   step6a  : so (f (p' x r v) <= 
>               reward t x oy ox' + Val (S t) n ox' or' ov' ps)
>   step6a  = leibniz
>               (\ fresh_var =>
>                   so (f (p' x r v) <= fresh_var))
>               step121 step5
>   step6 : so (reward t x y1 x1' + Val (S t) n x1' r1' v1' ps 
>               <= 
>               reward t x oy ox' + Val (S t) n ox' or' ov' ps
>              )
>   step6 = leibniz 
>             (\ fresh_var =>
>                  so (fresh_var <= 
>                  reward t x oy ox' + Val (S t) n ox' or' ov' ps))
>             step122 step6a
> {-
>   step7 : so (Val t (S n) x r v (p' :: ps) 
>               <= 
>               Val t (S n) x r v ((optExtension t n ps) :: ps)
>              )
>   step7 = step6 -- def. of Val
> -}

Now Bellman's principle of optimality states that optimal policy
sequences  extended with optimal extensions are themselves optimal:

> Bellman  :  (t : Nat) ->
>             (n : Nat) ->
>             (ps : PolicySeq (S t) n) ->
>             OptPolicySeq (S t) n ps ->
>             (p : Policy t (S n)) ->
>             OptExtension t n ps p ->
>             OptPolicySeq t (S n) (p :: ps)

The principle can be easily proved. One has

Val t (S n) x r v (p' :: ps')
  = {def. of Val, 
     y  = outl (p' x r v),
     x' = step t x y,
     r' = reachability1 x r y,
     v' = outr (p' x r v), 
     x' = step x (p' x)
    }  
reward t x y x' + Val (S t) n x' r' v' ps'
  <= {OptPolicySeq (S t) n ps, 
      monotonicity of +
     }
reward t x y x' + Val (S t) n x' r' v' ps
  = {def. of Val}  
Val t (S n) x r v (p' :: ps)
  <= {OptExtension t n ps p}
Val t (S n) x r v (p :: ps) 

or, equivalently:

Val t (S n) x r v (p' :: ps')
  <= {def. of Val, 
      OptPolicySeq ps, 
      monotonicity of +}
Val t (S n) x r v (p' :: ps)

  and
  
Val t (S n) x r v (p' :: ps)
  <= {OptExtension t n ps p}
Val t (S n) x r v (p :: ps) 

  -> {transitivity of <=}
  
Val t (S n) x r v (p' :: ps') <= Val t (S n) x r v (p :: ps) 

and a proof of Bellman's principle can be constructed as follows:

> Bellman t n ps ops p oep = 
>   opps where
>     opps : OptPolicySeq t (S n) (p :: ps)
>     opps Nil x r v impossible
>     opps (p' :: ps') x r v =
>       transitive_Float_lte step2 step3 where
>         y      :  Y t x
>         y      =  outl (p' x r v)
>         x'     :  X (S t)
>         x'     =  step t x y 
>         r'     :  Reachable x'
>         r'     =  reachableSpec1 x r y
>         v'     :  Viable n x'
>         v'     =  outr (p' x r v)
>         step1  :  so (Val (S t) n x' r' v' ps' <= Val (S t) n x' r' v' ps)
>         step1  =  ops ps' x' r' v'        
>         step2  :  so (Val t (S n) x r v (p' :: ps') <= Val t (S n) x r v (p' :: ps))
>         step2  =  monotone_Float_plus_lte (reward t x y x') step1
>         step3  :  so (Val t (S n) x r v (p' :: ps) <= Val t (S n) x r v (p :: ps))
>         step3  =  oep p' x r v

Bellman's principle suggests that the problem of computing an optimal
sequance of policies of length n (and thus, thank to OptLemma, optimal
sequences of controls of the same length) can be solved by computing n
optimal extensions by backwards induction. The following implementation
and lemma shows that this is in fact the case:

> backwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n

> backwardsInduction _ Z = Nil

> backwardsInduction t (S n) = ((optExtension t n ps) :: ps) where
>   ps : PolicySeq (S t) n
>   ps = backwardsInduction (S t) n


> BackwardsInductionLemma : (t : Nat) -> 
>                           (n : Nat) -> 
>                           OptPolicySeq t n (backwardsInduction t n)

> BackwardsInductionLemma _ Z = nilIsOptPolicySeq

> BackwardsInductionLemma t (S n) = 
>   Bellman t n ps ops p oep where
>     ps : PolicySeq (S t) n
>     ps = backwardsInduction (S t) n
>     ops : OptPolicySeq (S t) n ps
>     ops =  BackwardsInductionLemma (S t) n
>     p : Policy t (S n)
>     p = optExtension t n ps
>     oep : OptExtension t n ps p
>     oep = OptExtensionLemma t n ps
