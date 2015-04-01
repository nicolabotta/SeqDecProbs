> module ReachabilityViability


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

> reachable       :  X t -> Bool
> Reachable       :  X t -> Type

> Reachable x = so (reachable x)

which fulfill the specifications

> reachableSpec0  :  (x : X Z)         -> Reachable x
> reachableSpec1  :  (x : X t)         -> Reachable x ->
>                    (y : Y t x)       -> Reachable (step t x y)
> reachableSpec2  :  (x' : X (S t))    -> Reachable x' ->
>                    (x : X t ** (  Reachable x , 
>                                   (y : Y t x ** x' = step t x y)))

> {-

> Reachable       :  X t -> Type
> Reachable x = so (reachable x)
 
> reachableSpec0  :  (x : X Z) -> Reachable x
> reachableSpec1  :  (x : X t) ->
>                    Reachable x ->
>                    (y : Y t x) ->
>                    Reachable (step t x y)
> reachableSpec2  :  (x' : X (S t)) -> 
>                    Reachable x' ->
>                    (x : X t ** (Reachable x , (y : Y t x ** x' = step t x y)))

> -}
 
and

> viable : (n : Nat) -> X t -> Bool

> Viable : (n : Nat) -> X t -> Type
> Viable n x = so (viable n x)

> YV : (t : Nat) -> (n : Nat) -> X t -> Type
> YV t n x = (y : Y t x ** Viable n (step t x y))

which fulfill the specifications

> viableSpec0  :  (x : X t) -> Viable Z x
> viableSpec1  :  (x : X t) -> 
>                 Viable (S n) x ->
>                 YV t n x 
>                 -- (y : Y t x ** Viable n (step t x y))
> viableSpec2  :  (x : X t) ->
>                 YV t n x -> 
>                 -- (y : Y t x ** Viable n (step t x y)) ->
>                 Viable (S n) x



