# Contributions to a computational theory of policy advice and *avoidability*

Patrik Jansson (joint work with Nicola Botta and Cezar Ionescu)

* Application domain: Global Systems Science
* Sequential Decision Problems and Policy Advice
* Policy = function from state to control
* Control sequence is too limited
    * the sequence of controls, ``first turn left, then right, stop ten seconds at traffic light, then turn right'' is liable to lead to accidents
* Avoidability of certain future states - when rewards are hard to compute

----

* 1+2. Intro + Idris (functional, dependently typed, language)
* 3. Monadic sequential decision problems and policy advice
    * Deterministic decision processes
	    * States
		* Controls
		* Transition functions
		* Rewards
		* Decision processes
	* Non-deterministic decision processes
	* Stochastic decision processes
	* Monadic decision processes
	* Decision problems
    * Optimal policies
	* Viability and reachability (deterministic case)
	    * Viability
		* Policies revisited
		* Reachability
		* Policies revisited again
	* Viability and reachability: monadic case
	    * Viability and reachability
	* Policies and policy sequences revisited
	* A framework for monadic sequential decision problems
     	* Optimality of policy sequences
		* Bellman's optimality principle
		* Backwards induction
		* Can we compute optimal extensions?
    * Sequential decision problems and policy advice
* 4. Policy advice and avoidability
    * Policy advice and avoidability
    * Reachability from a state
    * Avoidability
    * Decidability of avoidability
    * Finite types and decidability
    * Decidability of avoidability, continued
    * Further thoughts
* 5+6. Conclusions & Future work
