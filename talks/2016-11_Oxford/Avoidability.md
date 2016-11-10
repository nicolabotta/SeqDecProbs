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

Seq. Dec. Prob: deterministic, time-independent

> State  : Type
> Ctrl   : (x : State) -> Type
> next   : (x : State) -> (y : Ctrl x) -> State
> reward : (x : State) -> (y : Ctrl x) -> (x' : State) -> Val

Seq. Dec. Prob: deterministic, time-dependent

> State  : (t : Nat) -> Type
> Ctrl   : (t : Nat) -> (x : State t) -> Type
> next   : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> State (1+t)
> reward : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> (x' : State (1+t)) -> Val

Seq. Dec. Prob: *monadic*, time-independent

> State  : Type
> Ctrl   : (x : State) -> Type
> nexts  : (x : State) -> (y : Ctrl x) -> M State   -- Monadic return value
> reward : (x : State) -> (y : Ctrl x) -> (x' : State) -> Val

Seq. Dec. Prob: monadic, time-dependent

> nexts : (t : Nat) -> (x : State t) -> (y : Ctrl t x) -> M (State (S t))
