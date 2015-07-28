> module Context

> import Data.So


> %default total


In the case of a time-dependent set of states and of a general
transition function, the context of a DP problem can be formalized in
terms of:

# A set of states |State|:

> State : Nat -> Type

# A set of controls or actions |Ctrl t x|:

> Ctrl : (t : Nat) -> State t -> Type

# A functor |M|

> M : Type -> Type

> Mmap   :  (alpha -> beta) -> M alpha -> M beta
> Mret   :  alpha -> M alpha
> Mbind  :  M alpha -> (alpha -> M beta) -> M beta

> -- unused functorSpec1  :  Mmap id = id
> -- unused functorSpec2  :  Mmap (f . g) = (Mmap f) . (Mmap g)

> -- unused monadSpec1  :  (Mmap f) . Mret = Mret . f
> -- unused monadSpec2  :  Mbind (Mret a) f = f a
> -- unused monadSpec3  :  Mbind ma Mret = ma
> -- unused monadSpec4  :  {f : a -> M b} -> {g : b -> M c} ->
> --                       Mbind (Mbind ma f) g = Mbind ma (\ a => Mbind (f a) g)

# A transition function:

> step : (t : Nat) -> (x : State t) -> Ctrl t x -> M (State (S t))

# A reward function:

> reward : (t : Nat) -> (x : State t) -> Ctrl t x -> State (S t) -> Float

For |M = Id|, |M = List| and |M = SimpleProb| one recovers the
deterministic case, the non-deterministic case and the stochastic
case.

|step t x y| yields an |M|-structure on |State (S t)|. For the specification
of |rechable| and |viable|, see section
S1302_ReachabilityViability.lidr, one has to assess whether a given
state is contained in |M|-structure (on states):

> MisIn : alpha -> M alpha -> Bool

> MareAllTrue : M Bool -> Bool

> -- unused Mspec1  :  (b : Bool) -> So (MareAllTrue (Mret b) == b)
> Mspec2  :  (mx : M alpha) -> (p : alpha -> Bool) ->
>            So (MareAllTrue (Mmap p mx)) ->
>            (x : alpha) -> So (x `MisIn` mx) -> So (p x)

> toSub      :  (ma : M alpha) -> M (a : alpha ** So (a `MisIn` ma))
> -- unused toSubSpec  :  (ma : M alpha) -> Mmap outl (toSub ma) = ma

> Mmeas     :  M Float -> Float
> MmeasMon  :  (f : State t -> Float) -> (g : State t -> Float) ->
>              ((x : State t) -> So (f x <= g x)) ->
>              (mx : M (State t)) -> So (Mmeas (Mmap f mx) <= Mmeas (Mmap g mx))

> Mreward        :  (t : Nat) -> (x : State t) -> Ctrl t x -> M Float
> Mreward t x y  =  Mmap (\ x' => reward t x y x') (step t x y)
