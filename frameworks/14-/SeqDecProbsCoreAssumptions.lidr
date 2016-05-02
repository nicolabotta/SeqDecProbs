> module SeqDecProbsCoreAssumptions

> import Sigma
> import SigmaOperations

> %default total
> %access public export
> %auto_implicits off
> -- %hide NonEmpty

> decl syntax "unused" {n} ":" [t] = postulate n : t


* Preliminaries

In this module we list the core assumptions underlying the theory of
sequential decision problems presented in "SeqDecProbCoreTheory.lidr".

The assumptions are implemented as holes (metavariables, forward
declarations, partial definitions, etc.). The idea is that users that
wish to apply the theory (typically, for computing provably optimal
solutions for a specific decision problem) will fill-in the holes by
providing problem-specific implementations.


* Sequential decision processes

A sequential decision problem (SDP) is specified in terms of, among
others, an underlying decision process.

In a decision process, a decision maker is required to perform a number
of decision steps. At each step, the decision maker is in (observes) a
state and is required to select a control (action, option). The idea is
that, upon selecting a control in a given state, the decision maker will
enter (observe) a new state. In a deterministic decision process, such
new state is uniquely defined in terms of the current decision step,
state and selected control. But in decision processes under uncertainty,
the decision maker only knows which new states are "possible" (again,
for a given decision step, "current" state and selected control) and,
perhaps, their probabilities. But it does not know not which one will
actually occur.

Thus, in order to specify a decision process, one has to first specify
what are the possible states at each decision step:

> State : (t : Nat) -> Type

Then, one has to explain which controls can be selected at a given step
and for a given state:

> Ctrl : (t : Nat) -> (x : State t) -> Type

Finally, one has to explain which "next" states are possible at a given
decision step, in a given state and for a selected control. In the
deterministic case, one could provide such explanation by defining a
stepping function

< step : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> State (S t)

But what if the decision process has uncertain outcomes? In this case,
we follow an approach originally proposed by Ionescu [1] and generalize
|step| to a monadic transition function:

> M : Type -> Type

> step    : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> M (State (S t))

For reasons that become clear immediately, |M| is is required fulfill

> fmap : {A, B : Type} -> (A -> B) -> M A -> M B
> postulate functorSpec1 : fmap . id = id
> postulate functorSpec2 : {A, B, C : Type} -> {f : B -> C} -> {g : A -> B} ->
>                          fmap (f . g) = (fmap f) . (fmap g)

In the above specification and throughout this file, we use postulates
to denote assumptions that are not strictly necessary for implementing
the theory. Thus, for the sake of the theory, |M| is not required to be
a functor.

In specific decision processes, we expect |M| to be |Id| (deterministic
SDP), |List| (non-deterministic SDP) or |Prob| (stochastic SDP). But our
assumptions are general enough to specify other kinds of decision
processes.


* Sequential decision problems

In order to obtain a decision problem, we introduce the additional
assumption that, with each transition from the current state to a new
state, the decision maker receives a certain reward (payoff, etc.)

> reward  : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> (x' : State (S t)) -> Nat

Since the original work of Bellman [1957], this has turned out to be a
very useful abstraction. The idea is that the decision maker seeks
controls that maximize the sum of the rewards obtained in a decision
process. In a deterministic case, implementing the above assumptions
completely defines a sequential decision problem. But whenever a
decision step has an uncertain outcome, uncertainties about "next"
states naturally yield uncertainties about rewards. In these cases, the
decision makes faces a number of possible rewards (one for each possible
next state) and has to explain how it measures such chances. In
stochastic decision problems, possible next states (and, therefore
possible rewards) are labelled with probabilities. In these cases,
possible rewards are often measured in terms of their expected value.
Here, again, we folow the approach proposed by Ionescu in [1] and
introduce a measure

> meas : M Nat -> Nat

that characterizes how the decision maker values uncertainties about
rewards in a single decision step. It is possible that a decision maker
values uncertainties according to different measures at different
decision steps. This could be easily formalized by generalising

< meas : M Nat -> Nat

to

< meas : (t : Nat) -> (x : State t) -> (M Nat -> Nat)

As it turns out, measure are essentially arbitrary. But they have to
satisfy a monotonicity condition

> measMon  :  {A : Type} ->
>             (f : A -> Nat) -> (g : A -> Nat) ->
>             ((a : A) -> (f a) `LTE` (g a)) ->
>             (ma : M A) -> (meas (fmap f ma)) `LTE` (meas (fmap g ma))

In a nutshell, |measMon| says that, if |ma| and |mb| are similar
|M|-structures and |ma| is smaller or equal to |mb|, than it cannot be
the case that the measure of |ma| is greater than the measure of |mb|.


* Solving sequential decision problems

Implementing the above holes defines a specific SDP unambiguously. But
in order to compute controls that provably maximize the sum of the
rewards over an arbitrary number of decision steps, we need some
additional assumptions. In particular, we need |M| to be a "monad":

> ret   :  {A : Type} -> A -> M A
> bind  :  {A, B : Type} -> M A -> (A -> M B) -> M B
> postulate monadSpec1   :  {A, B : Type} -> {f : A -> B} ->
>                           (fmap f) . ret = ret . f
> postulate monadSpec21  :  {A, B : Type} -> {f : A -> M B} -> {a : A} ->
>                           bind (ret a) f = f a
> postulate monadSpec22  :  {A : Type} -> {ma : M A} ->
>                           bind ma ret = ma
> postulate monadSpec23  :  {A, B, C : Type} -> {f : A -> M B} -> {g : B -> M C} -> {ma : M A} ->
>                           bind (bind ma f) g = bind ma (\ a => bind (f a) g)

> join  :  {A : Type} -> M (M A) -> M A
> join mma = bind mma id

and, more specifically, a "container" monad:

> Elem     : {A : Type} -> A -> M A -> Type
> NonEmpty : {A : Type} -> M A -> Type
> All      : {A : Type} -> (P : A -> Type) -> M A -> Type
> tagElem  : {A : Type} -> (ma : M A) -> M (Sigma A (\ a => a `Elem` ma))

> postulate elemNonEmptySpec0 : {A : Type} ->
>                               (a : A) -> (ma : M A) ->
>                               a `Elem` ma -> SeqDecProbsCoreAssumptions.NonEmpty ma

> postulate elemNonEmptySpec1 : {A : Type} ->
>                               (ma : M A) -> SeqDecProbsCoreAssumptions.NonEmpty ma -> 
>                               Sigma A (\ a => a `Elem` ma)

> postulate containerMonadSpec1 : {A : Type} -> {a : A} ->
>                                 a `Elem` (ret a)

> postulate containerMonadSpec2 : {A : Type} ->
>                                 (a : A) -> (ma : M A) -> (mma : M (M A)) ->
>                                 a `Elem` ma -> ma `Elem` mma -> a `Elem` (join mma)

> containerMonadSpec3 : {A : Type} -> {P : A -> Type} ->
>                       (a : A) -> (ma : M A) ->
>                       All P ma -> a `Elem` ma -> P a

> postulate tagElemSpec : {A : Type} ->
>                         (ma : M A) -> fmap outl (tagElem ma) = ma

The theory presented in "SeqDecProbCoreTheory.lidr" relies on two
further assumptions. Expressing these assumptions requires introducing
the notion of viability.

Intuitively, a state |x : State t| is viable for |n| steps if, in spite
of the uncertainties of the decision process, one can make |n| decision
steps starting from |x| without bumping into a dead end. Here, dead ends
are states for which no controls are available. In concrete decision
problems, they could represent exceptional outcomes: aborting a
computation, running out of fuel, being shot dead.

> Viable : {t : Nat} -> (n : Nat) -> State t -> Type

> Good : (t : Nat) -> (x : State t) -> (n : Nat) -> (Ctrl t x) -> Type
> -- Good t x n y = All (Viable {t = S t} n) (step t x y)
> Good t x n y = (SeqDecProbsCoreAssumptions.NonEmpty (step t x y), 
>                 All (Viable {t = S t} n) (step t x y))

> Good' : (t : Nat) -> (x : State t) -> (n : Nat) -> (Ctrl t x) -> Type
> Good' t x n y =  let mx = step t x y in
>                  (Exists (\ x' => Elem x' mx), All (Viable {t = S t} n) mx)

> GoodCtrl : (t : Nat) -> (x : State t) -> (n : Nat) -> Type
> GoodCtrl t x n = Sigma (Ctrl t x) (Good t x n)

> postulate viableSpec0 : {t : Nat} ->
>                         (x : State t) -> Viable Z x

> viableSpec1 : {t : Nat} -> {n : Nat} ->
>               (x : State t) -> Viable (S n) x -> GoodCtrl t x n

> postulate viableSpec2 : {t : Nat} -> {n : Nat} ->
>                         (x : State t) -> GoodCtrl t x n -> Viable (S n) x

A somehow orthogonal notion to viability is that of reachability. Even
though reachability is not needed for formalizing the last core
assumptions of the theory, we introduce it here. Intuitively, a state is
reachable if there are controls that allow for a path from some initial
state to that state. Thus, tautologically, every initial state is
reachable:

> Reachable : {t' : Nat} -> State t' -> Type

> postulate reachableSpec0 : (x : State Z) -> Reachable x

> reachableSpec1 : {t : Nat} ->
>                  (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) ->
>                  All (Reachable {t' = S t}) (step t x y)

> postulate reachableSpec2 : {t : Nat} ->
>                            (x' : State (S t)) -> Reachable x' ->
>                            Exists (\ x => (Reachable x , Exists (\ y => x' `Elem` (step t x y))))

With viability in place , we are now ready to express the last core
assumption at the core of the theory.

In "SeqDecProbCoreTheory.lidr" we are going to implement a generic form
(for all |State : (t : Nat) -> Type|, |Ctrl : (t : Nat) -> (x : State t)
-> Type|, |M : Type -> Type|, etc.) of the backwards induction algorithm
originally proposed by Bellman in 1957 [2]. The algorithm essentially
relies on being able to compute, for each possible state at a given
decision step |x : State t| a control in |Ctrl t x| that maximises an
arbitrary function from |Ctrl t x| to |Nat|. As it turns out, we can
relax a little bit this assumption and only require to be able to
compute such "optimal" controls only for those states in |State t| which
are viable for a certain number of steps. Thus, we assume that users
that want to apply the theory are able to implement two functions

> max    : {t : Nat} -> {n : Nat} ->
>          (x : State t) -> (Viable (S n) x) ->
>          (f : GoodCtrl t x n -> Nat) -> Nat

> argmax : {t : Nat} -> {n : Nat} ->
>          (x : State t) -> (Viable (S n) x) ->
>          (f : GoodCtrl t x n -> Nat) -> GoodCtrl t x n

that fulfill

> maxSpec : {t : Nat} -> {n : Nat} ->
>           (x : State t) -> (v : Viable (S n) x) ->
>           (f : GoodCtrl t x n -> Nat) -> (y : GoodCtrl t x n) ->
>           (f y) `LTE` (max x v f)

> argmaxSpec : {t : Nat} -> {n : Nat} ->
>              (x : State t) -> (v : Viable (S n) x) ->
>              (f : GoodCtrl t x n -> Nat) ->
>              max x v f = f (argmax x v f)


* Auxiliary functions

> |||
> ctrl : {t : Nat} -> {x : State t} -> {n : Nat} ->
>        GoodCtrl t x n -> Ctrl t x
> ctrl (MkSigma y _) = y

> |||
> good : {t : Nat} -> {x : State t} -> {n : Nat} ->
>        (y : GoodCtrl t x n) -> Good t x n (ctrl y)
> good (MkSigma _ p) = p

> |||
> allViable : {t : Nat} -> {x : State t} -> {n : Nat} -> {y : Ctrl t x} ->
>             (y : GoodCtrl t x n) -> All (Viable {t = S t} n) (step t x (ctrl y)) 
> -- allViable = good
> allViable (MkSigma y p) = snd p



* References

[1] Bellman, Richard; "Dynamic Programming", Princeton University Press,
    1957

[2] Ionescu, Cezar; "Vulnerability Modelling and Monadic Dynamical
    Systems", Freie Universitaet Berlin, 2009
