> module BackwardsInduction

> import Data.So

> import Float.Postulates

> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Reachability
> import DynamicProgramming.S1302_Viability
> import DynamicProgramming.S1303_OptimalPolicies
> import DynamicProgramming.S1304_MaxArgmax


If, for all reachable and viable |x : State t| and for all
|f : (y : Ctrl t x ** So (viable n (step t x y)))  ->  Float|,
we are able to select a control which maximises |f|, optimal sequences
of policies can be computed with Bellman's backwards induction
algorithm. This, in turn, follows from Bellman's optimality principle.

To express this principle, one needs the notion of optimal extension of
sequences of policies:

> OptExtension : (t : Nat) ->
>                (n : Nat) ->
>                PolicySeq (S t) n ->
>                Policy t (S n) ->
>                Type

> OptExtension t n ps p =
>   (p' : Policy t (S n)) ->
>   (x : State t) ->
>   (r : So (reachable x)) ->
>   (v : So (viable (S n) x)) ->
>   So (Mval t (S n) x r v (p' :: ps) <= Mval t (S n) x r v (p :: ps))


Under the assumptions put forward in S1304_MaxArgmax.lidr, it is easy to
compute optimal extensions for arbitrary sequences of policies:

> optExtension : (t : Nat) ->
>                (n : Nat) ->
>                PolicySeq (S t) n ->
>                Policy t (S n)

> optExtension t n ps = p where
>   p : Policy t (S n)
>   p x r v = yq where
>     yq : (y : Ctrl t x ** So (Mfeasible n x y))
>     yq = argmax n x r v f where
>       f' : (y : Ctrl t x ** So (Mfeasible n x y)) -> State (S t) -> Float
>       f' ycy x' = reward t x y x' + Mval (S t) n x' r' v' ps where
>         y : Ctrl t x
>         y = getWitness ycy
>         postulate x'ins : So (x' `MisIn` (step t x y))
>         r' : So (reachable {t = S t} x')
>         r' = reachableSpec1 x r y x' x'ins
>         v' : So (viable {t = S t} n x')
>         v' = Mspec2 (step t x y) (viable n) (getProof ycy) x' x'ins
>       f : (y : Ctrl t x ** So (Mfeasible n x y)) -> Float
>       f ycy = Mmeas (Mmap (f' ycy) (step t x (getWitness ycy)))

> postulate OptExtensionLemma :
>   (t : Nat) ->
>   (n : Nat) ->
>   (ps : PolicySeq (S t) n) ->
>   OptExtension t n ps (optExtension t n ps)


To prove that |optExtension t n ps| is indeed an optimal extension of |ps|
it is useful to recall:

Mval t (S n) x r v (p' :: ps)
  = {def. Mval,
     y  = getWitness (p' x r v)
     x' = step t x y
     r' = reachability1 x r y
     v' = getProof (p' x r v)
    }
reward t x y x' + Mval (S t) n x' r' v' ps
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
reward t x oy ox' + Mval (S t) n ox' or' ov' ps
  = {def. Mval}
Mval t (S n) x r v ((optExtension t n ps) :: ps)

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
reward t x y x' + Mval (S t) n x' r' v' ps
<=
reward t x oy ox' + Mval (S t) n ox' or' ov' ps
  => {def. Mval}
Mval t (S n) x r v (p' :: ps) <= Mval t (S n) x r v ((optExtension t n ps) :: ps)

-- > OptExtensionLemma t n ps p' x r v = step7 where
-- >   f : (y : Ctrl t x ** So (viable n (step t x y))) -> Float
-- >   f (y ** v') = reward t x y x' + Mval (S t) n x' r' v' ps where
-- >     x' : State (S t)
-- >     x' = step t x y
-- >     r' : So (reachable x')
-- >     r' = reachability1 x r y
-- >   step1 : So (f (p' x r v) <= max n x r v f)
-- >   -- step1 = maxSpec n x r v f (p' x r v)
-- >   step1 = ?lala1 -- Can't verify injectivity ...
-- >   step2 : So (max n x r v f == f (argmax n x r v f))
-- >   -- step2 = symmetric_Float_eqeq (argmaxSpec n x r v f)
-- >   step2 = ?lala2 -- Can't verify injectivity ...
-- >   step3 : So (max n x r v f <= f (argmax n x r v f))
-- >   step3 = sub_Float_eqeq_lte step2
-- >   step4 : So (f (p' x r v) <= f (argmax n x r v f))
-- >   step4 = transitive_Float_lte step1 step3
-- >   step4'' : argmax n x r v f = argmax n x r v f
-- >   step4'' = Refl
-- >   step4' : argmax n x r v f = (optExtension t n ps) x r v
-- >   step4' = believe_me step4''
-- >   step5 : So (f (p' x r v) <= f ((optExtension t n ps) x r v))
-- >   step5 = leibniz {P = \ a => So (f (p' x r v) <= f a)} step4' step4
-- >   y1 : Ctrl t x
-- >   y1 = getWitness (p' x r v)
-- >   x1' : State (S t)
-- >   x1' = step t x y1
-- >   r1' : So (reachable x1')
-- >   r1' = reachability1 x r y1
-- >   v1' : So (viable n x1')
-- >   v1' = getProof (p' x r v)
-- >   oy : Ctrl t x
-- >   oy = getWitness ((optExtension t n ps) x r v)
-- >   ox' : State (S t)
-- >   ox' = step t x oy
-- >   or' : So (reachable ox')
-- >   or' = reachability1 x r oy
-- >   ov' : So (viable n ox')
-- >   ov' = getProof ((optExtension t n ps) x r v)
-- >   step6 : So (reward t x y1 x1' + Mval (S t) n x1' r1' v1' ps
-- >               <=
-- >               reward t x oy ox' + Mval (S t) n ox' or' ov' ps
-- >              )
-- >   -- step6 = step5 -- def. of f
-- >   step6 = ?lala6 -- Stack overflow
-- >   step7 : So (Mval t (S n) x r v (p' :: ps)
-- >               <=
-- >               Mval t (S n) x r v ((optExtension t n ps) :: ps)
-- >              )
-- >   step7 = step6 -- def. of Mval


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

Mval t (S n) x r v (p' :: ps')
  = {def. of Mval,
     y  = getWitness (p' x r v),
     x' = step t x y,
     r' = reachability1 x r y,
     v' = getProof (p' x r v),
     x' = step x (p' x)
    }
reward t x y x' + Mval (S t) n x' r' v' ps'
  <= {OptPolicySeq (S t) n ps,
      monotonicity of +
     }
reward t x y x' + Mval (S t) n x' r' v' ps
  = {def. of Mval}
Mval t (S n) x r v (p' :: ps)
  <= {OptExtension t n ps p}
Mval t (S n) x r v (p :: ps)

or, equivalently:

Mval t (S n) x r v (p' :: ps')
  <= {def. of Mval,
      OptPolicySeq ps,
      monotonicity of +}
Mval t (S n) x r v (p' :: ps)

  and

Mval t (S n) x r v (p' :: ps)
  <= {OptExtension t n ps p}
Mval t (S n) x r v (p :: ps)

  -> {transitivity of <=}

Mval t (S n) x r v (p' :: ps') <= Mval t (S n) x r v (p :: ps)

and a proof of Bellman's principle can be constructed as follows:

> Bellman t n ps ops p oep = opps where
>   opps : OptPolicySeq t (S n) (p :: ps)
>   opps (p' :: ps') x r v = transitive_Float_lte step4 step5 where
>     ycy : (lala : Ctrl t x ** So (Mfeasible n x lala))
>     ycy = p' x r v
>     y : Ctrl t x
>     y = getWitness ycy
>     cy : So (Mfeasible n x y)
>     cy = getProof ycy
>     postulate x'ins : (x' : State (S t)) -> So (x' `MisIn` (step t x y))
>     r' : (x' : State (S t)) -> So (reachable {t = S t} x')
>     r' x' = reachableSpec1 x r y x' (x'ins x')
>     v' : (x' : State (S t)) -> So (viable {t = S t} n x')
>     v' x' = Mspec2 (step t x y) (viable n) cy x' (x'ins x')
>     step1 : (x' : State (S t)) -> So (Mval (S t) n x' (r' x') (v' x') ps'
>                                   <=
>                                   Mval (S t) n x' (r' x') (v' x') ps)
>     step1 x' = ops ps' x' (r' x') (v' x')
>     f : State (S t) -> Float
>     f x' = reward t x y x' + Mval (S t) n x' (r' x') (v' x') ps'
>     g : State (S t) -> Float
>     g x' = reward t x y x' + Mval (S t) n x' (r' x') (v' x') ps
>     step2 : (x' : State (S t)) -> So (f x' <= g x')
>     step2 x' = monotone_Float_plus_lte
>                -- {a1 = Mval (S t) n x' (r' x') (v' x') ps'}
>                -- {a2 = Mval (S t) n x' (r' x') (v' x') ps}
>                (reward t x y x')
>                (step1 x')
>     step3 : So (Mmeas (Mmap f (step t x y)) <= Mmeas (Mmap g (step t x y)))
>     step3 = MmeasMon {t = S t} f g step2 (step t x y)
>     step4 : So (Mval t (S n) x r v (p' :: ps') <= Mval t (S n) x r v (p' :: ps))
>     -- step4 = step3
>     -- the problem here is that f (g) and OptimalPolicies.Mval.f are
>     -- different functions !
>     step4 = believe_me Oh
>     step5 : So (Mval t (S n) x r v (p' :: ps) <= Mval t (S n) x r v (p :: ps))
>     step5 = oep p' x r v

Trying to define |f| and |g| in terms of the same global |val| function

-- > Bellman t n ps ops p oep = opps where
-- >   opps : OptPolicySeq t (S n) (p :: ps)
-- >   opps (p' :: ps') x r v = transitive_Float_lte step4 step5 where
-- >     ycy : (lala : Ctrl t x ** So (Mfeasible n x lala))
-- >     ycy = p' x r v
-- >     y : Ctrl t x
-- >     y = getWitness ycy
-- >     cy : So (Mfeasible n x y)
-- >     cy = getProof ycy
-- >     postulate x'ins : (x' : State (S t)) -> So (x' `MisIn` (step t x y))
-- >     r' : (x' : State (S t)) -> So (reachable x')
-- >     r' x' = reachability1 x r y x' (x'ins x')
-- >     v' : (x' : State (S t)) -> So (viable n x')
-- >     v' x' = Mspec2 (step t x y) (viable n) cy x' (x'ins x')
-- >     step1 : (x' : State (S t)) -> So (Mval (S t) n x' (r' x') (v' x') ps'
-- >                                   <=
-- >                                   Mval (S t) n x' (r' x') (v' x') ps)
-- >     step1 x' = ops ps' x' (r' x') (v' x')
-- >     f : State (S t) -> Float
-- >     f = val t n x r v p' ps'
-- >     g : State (S t) -> Float
-- >     g = val t n x r v p' ps
-- >     step2 : (x' : State (S t)) -> So (f x' <= g x')
-- >     step2 x' = monotone_Float_plus_lte (reward t x y x') (step1 x')
-- >     step3 : So (Mmeas (Mmap f (step t x y)) <= Mmeas (Mmap g (step t x y)))
-- >     step3 = MmeasMon f g step2 (step t x y)
-- >     step4 : So (Mval t (S n) x r v (p' :: ps') <= Mval t (S n) x r v (p' :: ps))
-- >     -- step4 = step3
-- >     -- the problem here is that f (g) and OptimalPolicies.Mval.f are
-- >     -- different functions !
-- >     step4 = believe_me Oh
-- >     step5 : So (Mval t (S n) x r v (p' :: ps) <= Mval t (S n) x r v (p :: ps))
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
