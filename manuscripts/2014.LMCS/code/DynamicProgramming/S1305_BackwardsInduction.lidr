> module BackwardsInduction


> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Reachability
> import DynamicProgramming.S1302_Viability
> import DynamicProgramming.S1303_OptimalPolicies
> import DynamicProgramming.S1304_MaxArgmax


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


Under the assumptions put forward in S1304_MaxArgmax.lidr, it is easy to
compute optimal extensions for arbitrary sequences of policies:

> optExtension : (t : Nat) -> 
>                (n : Nat) -> 
>                PolicySeq (S t) n -> 
>                Policy t (S n)

> optExtension t n ps = p where
>   p : Policy t (S n)
>   p x r v = yq where 
>     yq : (y : Y t x ** so (feasible n x y))
>     yq = argmax n x r v f where
>       f' : (y : Y t x ** so (feasible n x y)) -> X (S t) -> Float
>       f' ycy x' = reward t x y x' + Val (S t) n x' r' v' ps where
>         y : Y t x
>         y = getWitness ycy
>         postulate x'ins : so (x' `MisIn` (step t x y))
>         r' : so (reachable {t = S t} x')
>         r' = reachableSpec1 x r y x' x'ins
>         v' : so (viable {t = S t} n x')
>         v' = Mspec2 (step t x y) (viable n) (getProof ycy) x' x'ins
>       f : (y : Y t x ** so (feasible n x y)) -> Float
>       f ycy = meas (Mmap (f' ycy) (step t x (getWitness ycy)))

> postulate OptExtensionLemma : 
>   (t : Nat) -> 
>   (n : Nat) -> 
>   (ps : PolicySeq (S t) n) ->
>   OptExtension t n ps (optExtension t n ps)


To prove that |optExtension t n ps| is indeed an optimal extension of |ps|
it is useful to recall:

Val t (S n) x r v (p' :: ps) 
  = {def. Val, 
     y  = getWitness (p' x r v)
     x' = step t x y
     r' = reachability1 x r y
     v' = getProof (p' x r v)
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
     oy  = getWitness (optExtension t n ps x r v),
     ox' = step t x oy,
     or' = reachability1 x r oy,
     ov' = getProof (optExtension t n ps x r v)
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
      y  = getWitness (p' x r v),
      x' = step t x y,
      r' = reachability1 x r y,
      v' = getProof (p' x r v), 
      oy  = getWitness (optExtension t n ps x r v),
      ox' = step t x oy,
      or' = reachability1 x r oy,
      ov' = getProof (optExtension t n ps x r v)  
     }
reward t x y x' + Val (S t) n x' r' v' ps 
<= 
reward t x oy ox' + Val (S t) n ox' or' ov' ps
  => {def. Val}
Val t (S n) x r v (p' :: ps) <= Val t (S n) x r v ((optExtension t n ps) :: ps)

-- > OptExtensionLemma t n ps p' x r v = step7 where
-- >   f : (y : Y t x ** so (viable n (step t x y))) -> Float  
-- >   f (y ** v') = reward t x y x' + Val (S t) n x' r' v' ps where
-- >     x' : X (S t)
-- >     x' = step t x y
-- >     r' : so (reachable x')
-- >     r' = reachability1 x r y
-- >   step1 : so (f (p' x r v) <= max n x r v f)  
-- >   -- step1 = maxSpec n x r v f (p' x r v)
-- >   step1 = ?lala1 -- Can't verify injectivity ...
-- >   step2 : so (max n x r v f == f (argmax n x r v f))
-- >   -- step2 = symmetric_Float_eqeq (argmaxSpec n x r v f)
-- >   step2 = ?lala2 -- Can't verify injectivity ...
-- >   step3 : so (max n x r v f <= f (argmax n x r v f))
-- >   step3 = sub_Float_eqeq_lte step2
-- >   step4 : so (f (p' x r v) <= f (argmax n x r v f))
-- >   step4 = transitive_Float_lte step1 step3
-- >   step4'' : argmax n x r v f = argmax n x r v f 
-- >   step4'' = refl
-- >   step4' : argmax n x r v f = (optExtension t n ps) x r v
-- >   step4' = believe_me step4''
-- >   step5 : so (f (p' x r v) <= f ((optExtension t n ps) x r v))
-- >   step5 = leibniz {P = \ a => so (f (p' x r v) <= f a)} step4' step4
-- >   y1 : Y t x
-- >   y1 = getWitness (p' x r v)
-- >   x1' : X (S t)
-- >   x1' = step t x y1
-- >   r1' : so (reachable x1')
-- >   r1' = reachability1 x r y1
-- >   v1' : so (viable n x1')
-- >   v1' = getProof (p' x r v)
-- >   oy : Y t x
-- >   oy = getWitness ((optExtension t n ps) x r v)
-- >   ox' : X (S t)
-- >   ox' = step t x oy
-- >   or' : so (reachable ox')
-- >   or' = reachability1 x r oy
-- >   ov' : so (viable n ox')
-- >   ov' = getProof ((optExtension t n ps) x r v)
-- >   step6 : so (reward t x y1 x1' + Val (S t) n x1' r1' v1' ps 
-- >               <= 
-- >               reward t x oy ox' + Val (S t) n ox' or' ov' ps
-- >              )
-- >   -- step6 = step5 -- def. of f
-- >   step6 = ?lala6 -- Stack overflow
-- >   step7 : so (Val t (S n) x r v (p' :: ps) 
-- >               <= 
-- >               Val t (S n) x r v ((optExtension t n ps) :: ps)
-- >              )
-- >   step7 = step6 -- def. of Val


Now Bellman's principle of optimality states that optimal policy
sequences  extended with optimal extensions are themselves optimal:

> Bellman : (t : Nat) ->
>           (n : Nat) ->
>           (ps : PolicySeq (S t) n) ->
>           OptPolicySeq (S t) n ps ->
>           (p : Policy t (S n)) ->
>           OptExtension t n ps p ->
>           OptPolicySeq t (S n) (p :: ps)

The principle can be easily proved. One has

Val t (S n) x r v (p' :: ps')
  = {def. of Val, 
     y  = getWitness (p' x r v),
     x' = step t x y,
     r' = reachability1 x r y,
     v' = getProof (p' x r v), 
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

> Bellman t n ps ops p oep = opps where
>   opps : OptPolicySeq t (S n) (p :: ps)
>   opps (p' :: ps') x r v = transitive_Float_lte 
>                                         {a1 = Val t (S n) x r v (p' :: ps')}
>                                         {a2 = Val t (S n) x r v (p' :: ps)}
>                                         {a3 = Val t (S n) x r v (p :: ps)}
>                                         step4 step5 where
>     ycy : (lala : Y t x ** so (feasible n x lala))
>     ycy = p' x r v
>     y : Y t x
>     y = getWitness ycy
>     cy : so (feasible n x y)
>     cy = getProof ycy 
>     postulate x'ins : (x' : X (S t)) -> so (x' `MisIn` (step t x y))
>     r' : (x' : X (S t)) -> so (reachable {t = S t} x')
>     r' x' = reachableSpec1 x r y x' (x'ins x')
>     v' : (x' : X (S t)) -> so (viable {t = S t} n x')
>     v' x' = Mspec2 (step t x y) (viable n) cy x' (x'ins x')
>     step1 : (x' : X (S t)) -> so (Val (S t) n x' (r' x') (v' x') ps' 
>                                   <= 
>                                   Val (S t) n x' (r' x') (v' x') ps)
>     step1 x' = ops ps' x' (r' x') (v' x') 
>     f : X (S t) -> Float
>     f x' = reward t x y x' + Val (S t) n x' (r' x') (v' x') ps'
>     g : X (S t) -> Float
>     g x' = reward t x y x' + Val (S t) n x' (r' x') (v' x') ps
>     step2 : (x' : X (S t)) -> so (f x' <= g x')
>     step2 x' = monotone_Float_plus_lte 
>                {a1 = Val (S t) n x' (r' x') (v' x') ps'} 
>                {a2 = Val (S t) n x' (r' x') (v' x') ps} 
>                (reward t x y x') 
>                (step1 x')
>     step3 : so (meas (Mmap f (step t x y)) <= meas (Mmap g (step t x y)))
>     step3 = measMon {t = S t} f g step2 (step t x y)
>     step4 : so (Val t (S n) x r v (p' :: ps') <= Val t (S n) x r v (p' :: ps))
>     -- step4 = step3 
>     -- the problem here is that f (g) and OptimalPolicies.Val.f are
>     -- different functions !
>     step4 = believe_me oh
>     step5 : so (Val t (S n) x r v (p' :: ps) <= Val t (S n) x r v (p :: ps))
>     step5 = oep p' x r v

Trying to define |f| and |g| in terms of the same global |val| function

-- > Bellman t n ps ops p oep = opps where
-- >   opps : OptPolicySeq t (S n) (p :: ps)
-- >   opps (p' :: ps') x r v = transitive_Float_lte step4 step5 where
-- >     ycy : (lala : Y t x ** so (feasible n x lala))
-- >     ycy = p' x r v
-- >     y : Y t x
-- >     y = getWitness ycy
-- >     cy : so (feasible n x y)
-- >     cy = getProof ycy 
-- >     postulate x'ins : (x' : X (S t)) -> so (x' `MisIn` (step t x y))
-- >     r' : (x' : X (S t)) -> so (reachable x')
-- >     r' x' = reachability1 x r y x' (x'ins x')
-- >     v' : (x' : X (S t)) -> so (viable n x')
-- >     v' x' = Mspec2 (step t x y) (viable n) cy x' (x'ins x')
-- >     step1 : (x' : X (S t)) -> so (Val (S t) n x' (r' x') (v' x') ps' 
-- >                                   <= 
-- >                                   Val (S t) n x' (r' x') (v' x') ps)
-- >     step1 x' = ops ps' x' (r' x') (v' x') 
-- >     f : X (S t) -> Float
-- >     f = val t n x r v p' ps' 
-- >     g : X (S t) -> Float
-- >     g = val t n x r v p' ps
-- >     step2 : (x' : X (S t)) -> so (f x' <= g x')
-- >     step2 x' = monotone_Float_plus_lte (reward t x y x') (step1 x')
-- >     step3 : so (meas (Mmap f (step t x y)) <= meas (Mmap g (step t x y)))
-- >     step3 = measMon f g step2 (step t x y)
-- >     step4 : so (Val t (S n) x r v (p' :: ps') <= Val t (S n) x r v (p' :: ps))
-- >     -- step4 = step3 
-- >     -- the problem here is that f (g) and OptimalPolicies.Val.f are
-- >     -- different functions !
-- >     step4 = believe_me oh
-- >     step5 : so (Val t (S n) x r v (p' :: ps) <= Val t (S n) x r v (p :: ps))
-- >     step5 = oep p' x r v


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


----------- APPENDIX --------------

-- > BackwardsInduction.foo = proof {
-- >   intros;
-- >   let res = p' x r v;
-- >   let res' = getProof res;
-- >   compute;
-- >   refine res';
-- > }
