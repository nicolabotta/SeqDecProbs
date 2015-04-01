Idris code related to the research project "A computational theory of policy advice and avoidability".

Nicola Botta, Patrik Jansson, Cezar Ionescu

http://www.idris-lang.org/

2015-03-27: Paper submitted to
* Journal:  Mathematical Social Sciences
* Corresponding Author:  Nicola Botta
* Co-Authors:  Patrik Jansson, Dr. Prof.; Cezar Ionescu, Dr.
* Title:  A computational theory of policy advice and avoidability
* [A full text pre-print (before refereeing) is available](http://www.cse.chalmers.se/~patrikj/papers/CompTheoryPolicyAdviceAvoidability_preprint.pdf)

Some associated code is also in https://github.com/patrikja/SeqDecProb_Agda/

----------------

An earlier paper about Sequential Decision Problems was submitted already August 2014.

2014-08-15: Paper submitted
* Title: Sequential decision problems, dependent types and generic solutions
* Journal: [Logical Methods in Computer Sciennce](http://www.lmcs-online.org/index.php)
* Corresponding author: Patrik Jansson
* Authors: Nicola Botta, Patrik Jansson, Cezar Ionescu, David Christiansen, Edwin Brady
* [A full text pre-print (before refereeing) is available](http://www.cse.chalmers.se/~patrikj/papers/SeqDecProbDepType_LMCS_2014_preprint.pdf)
* Abstract:	We present a computer-checked generic implementation for solving finite-horizon sequential decision problems. This is a wide class of problems, including inter-temporal optimizations, knapsack, optimal bracketing, scheduling, etc. The implementation can handle time-step dependent control and state spaces, and monadic representations of uncertainty (such as stochastic, non-deterministic, fuzzy, or combinations thereof). This level of genericity is achievable in a programming language with dependent types (we have used both Idris and Agda). Dependent types are also the means that allow us to obtain a formalization and computer-checked proof of the central component of our implementation: Bellman's principle of optimality and the associated backwards induction algorithm. The formalization clarifies certain aspects of backwards induction and, by making explicit notions such as viability and reachability, can serve as a starting point for a theory of controllability of monadic dynamical systems, commonly encountered in, e.g., climate impact research.
