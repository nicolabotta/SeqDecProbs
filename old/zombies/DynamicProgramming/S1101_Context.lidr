> module Context

> %default total


In the simplest case of a constant (in contrast to time-dependent) set
of states and of a deterministic transition function, the context of a
DP problem can be formalized in terms of:

# A constant set of states |X|:

> X : Type

# For each |x : X|, a set of controls or actions |Y x|:

> -- partial Y : (x : X) -> Type
> Y : (x : X) -> Type

The idea is that |Y x| are those actions which are feasible (admissible)
in |x|. 

# For each |x : X|, |y : Y x|, a deterministic transition function:

> step : (x : X) -> (y : Y x) -> X

The idea is that selecting a feasible control in a state yields a well
defined new state. In S130 we will relax this assumption and consider
transition functions that associate to any |x : X| and |y : Y x| some
structure on |X|, e.g., |List X| (non-deterministic case) or |SimpleProb
X| (stochastic case).

# For each |x : X|, |y : Y x| and |x' : X|, a reward function:

> reward : (x : X) -> (y : Y x) -> (x' : X) -> Float

The idea is that each state transition yields a certain reward. For the
time being, we assume rewards to be |Float|s but this assumption can be
easily relaxed. In general, the reward depends on the state in which the
transition occurs, on the control selected in that state (e.g., via
control costs) and on the new state.

In DP, one is interested in sequences of (feasible) controls that
maximise the sum of the rewards obtained in a finite number of steps
when starting from a given x : X. We formalise this notion in section
OptimalControls. 
