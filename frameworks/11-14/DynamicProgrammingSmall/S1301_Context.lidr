> module Context

> import Data.So

> %default total


In the case of a time-dependent set of states and of a general
transition function, the context of a DP problem can be formalized in
terms of:

# A set of states |X|:

> X : Nat -> Type

# A set of controls or actions |Y t x|:

> Y : (t : Nat) -> X t -> Type

# A functor |M|

> M : Type -> Type

> Mmap : (alpha -> beta) -> M alpha -> M beta

> Mret : alpha -> M alpha

> Mbind : M alpha -> (alpha -> M beta) -> M beta

Todo: write specifications for |Mret| and |Mbind|


# A transition function:

> step : (t : Nat) -> (x : X t) -> Y t x -> M (X (S t))

# A reward function:

> reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Float

For |M = Id|, |M = List| and |M = SimpleProb| one recovers the
deterministic case, the non-deterministic case and the stochastic
case.

|step t x y| yields an |M|-structure on |X (S t)|. For the specification
of |rechable| and |viable|, see section
S1302_ReachabilityViability.lidr, one has to assess whether a given
state is contained in |M|-structure (on states):

> MisIn : X (S t) -> M (X (S t)) -> Bool

> MareAllTrue : M Bool -> Bool

> Mspec1 : (b : Bool) -> So (MareAllTrue (Mret b) == b)

> Mspec2 : (mx : M (X (S t))) ->
>          (p : X (S t) -> Bool) ->
>          So (MareAllTrue (Mmap p mx)) ->
>          (x : X (S t)) ->
>          So (x `MisIn` mx) ->
>          So (p x)

Because |M| is a functor, an |M|-structure on |X (S t)| induces an
|M|-structure on rewards:

Mmap (reward t x y) (step t x y) : M Float

One can extend all the results and algorithms derived for the
deterministic case if one assumes that the controler has a measure for
evaluating such |M|-structure:

> meas : M Float -> Float

and that such measure satisfies the following monotonicity condition,
see S130...

> measMon : (f : X t -> Float) -> 
>           (g : X t -> Float) -> 
>           ((x : X t) -> So (f x <= g x)) ->
>           (mx : M (X t)) -> 
>           So (meas (Mmap f mx) <= meas (Mmap g mx))


