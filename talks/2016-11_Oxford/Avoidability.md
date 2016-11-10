# Contributions to a computational theory of policy advice and *avoidability*

Patrik Jansson (joint work with Nicola Botta and Cezar Ionescu)

* Application domain: Global Systems Science
* Sequential Decision Problems and Policy Advice
* Policy = function from state to control
* Control sequence is too limited
    * the sequence of controls, ``first turn left, then right, stop ten seconds at traffic light, then turn right'' is liable to lead to accidents
* Avoidability of certain future states - when rewards are hard to compute

----

Paper outline:

* 1+2. Intro + Preliminaries                                [p1-8]
    * GSS background and motivation
    * Idris (functional, dependently typed, language)
* 3. Monadic sequential decision problems and policy advice [p9-33]
    * Deterministic decision processes                      [p9-10]
	    * States
		* Controls
		* Transition functions
		* Rewards
		* Decision processes
	* Non-deterministic decision processes                  [p11]
	* Stochastic decision processes                         [p12]
	* Monadic decision processes                            [p13-14]
	* Decision problems                                     [p15-17]
    * Optimal policies                                      [p18]
	* Viability and reachability (the deterministic case)   [p19-21]
	    * Viability
		* Policies revisited
		* Reachability
		* Policies revisited again
	* Viability and reachability (the monadic case)         [p22-23]
	    * Viability and reachability
	* Policies and policy sequences revisited               [p24-25]
	* A framework for monadic sequential decision problems  [p26-30]
     	* Optimality of policy sequences
		* Bellman's optimality principle
		* Backwards induction
		* Can we compute optimal extensions?
    * Sequential decision problems and policy advice        [p31-33]
* 4. Policy advice and avoidability                         [p34-41]
    * Policy advice and avoidability
    * Reachability from a state
    * Avoidability
    * Decidability of avoidability
    * Finite types and decidability
    * Decidability of avoidability, continued
    * Further thoughts
* 5+6. Conclusions & Future work                            [p42]
* Appendix A-F                                              [p43-47]
* References                                                [p48-50]

----------------

## Seq. Dec. Prob: deterministic, time-independent

> State  : Type
> Ctrl   : (x : State) -> Type
> next   : (x : State) -> (y : Ctrl x) -> State
> reward : (x : State) -> (y : Ctrl x) -> (x' : State) -> Val

## Seq. Dec. Prob: deterministic, time-dependent

> State  : (t : Nat) -> Type
> Ctrl   : (t : Nat) -> (x : State t) -> Type
> next   : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> State (1+t)
> reward : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> (x' : State (1+t)) -> Val

## Seq. Dec. Prob: *monadic*, time-independent

> State  : Type
> Ctrl   : (x : State) -> Type
> nexts  : (x : State) -> (y : Ctrl x) -> M State   -- Monadic return value
> reward : (x : State) -> (y : Ctrl x) -> (x' : State) -> Val

## Seq. Dec. Prob: monadic, time-dependent

> nexts : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> M (State (S t))

I will call a record of (M, State, Ctrl, nexts, reward) a "SeqDecProb". (Some more components are needed: |meas : M Val -> Val|, some proofs, etc.)

What is "the problem" that we would like to solve?

Given a SeqDecProb, compute an *optimal policy sequence* for a given
time horizon |n|.

## Policy

> Policy    :  (t : Nat) -> Type
> Policy t  =  (x : State t) -> Ctrl t x

## Policy Sequence

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  PolicySeq t Z
>   (::)  :  Policy t -> PolicySeq (S t) n -> PolicySeq t (S n)

## Value of a Policy Sequence

> val : (x : State t) -> (ps : PolicySeq t n) -> Val
> val {t} {n = Z} x ps = zero
> val {t} {n = S m} x (p :: ps) = meas (fmap f mx') where
>   y     :  Ctrl t x
>   y     =  p x
>   f     :  State (S t) -> Val
>   f x'  =  reward t x y x'  +  val x' ps
>   mx'   :  M (State (S t))
>   mx'   =  nexts t x y

## Optimal Policy Sequence

> OptPolicySeq : PolicySeq t n -> Type
> OptPolicySeq {t} {n} ps  =  (ps' : PolicySeq t n) -> (x : State t) ->
                              (val x ps') <= (val x ps)

## Skip for this talk: Reachable, Viable

## Bellman's principle

To compute optimal policy sequences step by step

> Bellman  :  (ps  :  PolicySeq (S t) m)  ->   OptPolicySeq ps ->
>             (p   :  Policy t (S m))     ->   OptExt ps p ->
>             OptPolicySeq (p :: ps)

> optExt : PolicySeq (S t) n -> Policy t (S n)
> postulate optExtLemma : (ps : PolicySeq (S t) n) -> OptExt ps (optExt ps)

> backwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n
> backwardsInduction t  Z     =  Nil
> backwardsInduction t (S n)  =  optExt ps :: ps where
>   ps  :  PolicySeq (S t) n
>   ps  =  backwardsInduction (S t) n

The key is the function |optExt| which, from the end, step by step
extends the sequence of policies.

(TODO: an example would be great at this stage.)

## Computing |optExt|

Basically we need to implement |argmax| for |val| to pick the best
control for this step. This is easy for finite |Ctrl t x| and can be
done (or approximated) also for infinite control space for certain
classes of reward functions.

## Summing up

We now have a theory for SeqDecProbs and a generic implementation of
backwards induction with a proof of correctness. Next we look at one
possibility of making it more applicable by removing the requirement
to provide a |reward| function.

## Avoidability

Computing rewards can be difficult - what can be done without the
|reward| function?

If we know that certain future state must be *avoided* completely, we
can use that as a kind of "boolean reward function".

In the rather general setting of (M, State, Ctrl, nexts) it takes a
bit of work to come up with a good definition of "avoidable".

We start with "reachable":

> CanReach : State t -> State t' -> Type

this is a relation between states now (at step |t|) and states later
(at step |t'|).

  x --{c'}-> ... -> x'    -- there is a path with some controls

Then, for |x'| to be avoidable, we need another state |x''|, also
reachable from |x|.

  x --{c''}-> ... -> x''  -- there is a path with some (other) controls

To make this rigorous we also need to take into account
* viability
* the monadic structure (paths in trees)
