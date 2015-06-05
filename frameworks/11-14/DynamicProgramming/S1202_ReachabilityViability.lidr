> module ReachabilityViability

> import Data.So

> import Util.VectExtensions1
> import DynamicProgramming.S1201_Context


> %default total

For a given state |x : X t|, the set of feasible controls |Y t x| and the
transition function define the set of possible successors of |x|. These
are the states that can be reached from |x| in one step.

Similarly, given |x' : X t|, |Y : (t : Nat) -> X t -> Type| and the
transition function, one can compute the set of possible predecessors of
|x'|.

These sets can used to introduce the notions of reachability and
viability. We say that every state is reachable in zero steps and that
|x'| is reachable in |S m| steps if |x'| has (at least) a predecessor
which is reachable in |m| steps. Similarly, we say that |x| is viable |S
n| steps if |x| has (at least) a successor which is viable for |n|
steps.

Definitions of reachability and viability which are based on the notions
of predecessor and successor are recursive. They can potentially trigger
time consuming computations at type checking and prevent efficient
tabulation. 

We provide such definitions in "S1202_ReachabilityViabilityDefaults". In
this section we just give a specification for reachability and viability
as predicates: |reachable| and |viable|. This approach allows us to
defer the implementation of |reachable| and |viable| to applications (as
done for |X|, |Y|, |step|, |reward|, |max|, |argmax| etc.) and to take
advantage of more efficient implementations users might be able to
provide for these predicates. An example of such implementations is
given in "...".

In a nutshell, we require client of this module to implement

> reachable : X t -> Bool

which fulfill the specifications

> reachableSpec0 : (x : X Z) -> So (reachable x)

> reachableSpec1 : (x : X t) ->
>                  So (reachable x) ->
>                  (y : Y t x) ->
>                  -- So (reachable {t = S t} (step t x y))
>                  So (reachable (step t x y))

> reachableSpec2 : (x' : X (S t)) -> 
>                  -- So (reachable {t = S t} x') ->
>                  So (reachable x') ->
>                  (x : X t ** (y : Y t x ** (So (reachable x), x' = step t x y)))

or, alternatively:

-- > data Reachable : X t -> Type where
-- >   Reachable_Z  : {x : X Z} -> Reachable x
-- >   Reachable_St : {x : X t} -> 
-- >                  Reachable x -> 
-- >                  (y : Y t x) ->
-- >                  Reachable {t = S t} (step t x y)

-- > reachableSpec  : (x : X t) -> Reachable x -> So (reachable x)
-- > reachableSpec' : (x : X t) -> So (reachable x) -> Reachable x

and

> viable : (n : Nat) -> X t -> Bool

which fulfill the specifications

> viableSpec0 : (x : X t) -> So (viable Z x)

> viableSpec1 : (x : X t) -> 
>               So (viable (S n) x) -> 
>               -- (y : Y t x ** So (viable {t = S t} n (step t x y)))
>               (y : Y t x ** So (viable n (step t x y)))

> viableSpec2 : (x : X t) -> 
>               -- (y : Y t x ** So (viable {t = S t} n (step t x y))) ->
>               (y : Y t x ** So (viable n (step t x y))) ->
>               So (viable (S n) x)

or, alternatively:

-- > data Viable : Nat -> X t -> Type where
-- >   Viable_Z  :  {x : X t} -> Viable Z x
-- >   Viable_Sn :  (x : X t) -> 
-- >                (y : Y t x) -> 
-- >                Viable {t = S t} n (step t x y) -> 
-- >                Viable (S n) x

-- > viableSpec  : (x : X t) -> Viable n x -> So (viable n x)
-- > viableSpec' : (x : X t) -> So (viable n x) -> Viable n x

-- > Viability1   :  (x : X t) -> Viable (S n) x -> 
-- >                 (y : Y t x ** Viable {t = S t} n (step t x y))
-- > Viability1 x Viable_Z impossible
-- > Viability1 x (Viable_Sn _ y vs) = (y ** vs)



