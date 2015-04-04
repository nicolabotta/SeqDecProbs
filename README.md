Idris code related to the research project "A computational theory of policy advice and avoidability".
(using dependent types in the Sequential Decision Problems domain)

Nicola Botta, Patrik Jansson, Cezar Ionescu

http://www.idris-lang.org/

2015-03-27: Paper submitted to
* Journal:  [Mathematical Social Sciences](http://www.journals.elsevier.com/mathematical-social-sciences/) (a [RoMEO Green](http://www.sherpa.ac.uk/romeo/search.php?issn=0165-4896) journal)
* Corresponding Author:  Nicola Botta
* Authors: Nicola Botta, Patrik Jansson, Cezar Ionescu
* Title:  A computational theory of policy advice and avoidability
* [A full text pre-print (before refereeing) is available](http://www.cse.chalmers.se/~patrikj/papers/CompTheoryPolicyAdviceAvoidability_preprint.pdf)
* Abstract: We present a mathematical theory of policy advice and avoidability. More specifically, we formalize the notions of decision process, decision problem and policy, and propose a novel approach for assisting decision making. The latter is based on the idea of avoidability. We formalize avoidability as a relation between current and future states, investigate under which conditions this relation is decidable and propose a generic procedure for assessing avoidability. The theory is both formal and constructive and makes extensive use of the correspondence between dependent types and logical propositions. Decidable judgments are obtained through computations. Thus, it is a computational theory. Our main motivation comes from climate impact research and our perspective is that of computing science. But the theory we propose is completely generic and we understand our contribution as one to global system science.

The complete code is in the top level directory and some code in [2015.MSS](manuscripts/2015.MSS/).

Some associated code is also in https://github.com/patrikja/SeqDecProb_Agda/

----------------

An earlier paper about Sequential Decision Problems was submitted already August 2014.

2014-08-15: Paper submitted
* Title: Sequential decision problems, dependent types and generic solutions
* Journal: [Logical Methods in Computer Sciennce](http://www.lmcs-online.org/index.php) (a [RoMEO Green](http://www.sherpa.ac.uk/romeo/search.php?issn=1860-5974) journal)
* Corresponding author: Patrik Jansson
* Authors: Nicola Botta, Patrik Jansson, Cezar Ionescu, David Christiansen, Edwin Brady
* [A full text pre-print (before refereeing) is available](http://www.cse.chalmers.se/~patrikj/papers/SeqDecProbDepType_LMCS_2014_preprint.pdf)
* Abstract:	We present a computer-checked generic implementation for solving finite-horizon sequential decision problems. This is a wide class of problems, including inter-temporal optimizations, knapsack, optimal bracketing, scheduling, etc. The implementation can handle time-step dependent control and state spaces, and monadic representations of uncertainty (such as stochastic, non-deterministic, fuzzy, or combinations thereof). This level of genericity is achievable in a programming language with dependent types (we have used both Idris and Agda). Dependent types are also the means that allow us to obtain a formalization and computer-checked proof of the central component of our implementation: Bellman's principle of optimality and the associated backwards induction algorithm. The formalization clarifies certain aspects of backwards induction and, by making explicit notions such as viability and reachability, can serve as a starting point for a theory of controllability of monadic dynamical systems, commonly encountered in, e.g., climate impact research.

The complete code is in [2014.LMCS](manuscripts/2014.LMCS/).
