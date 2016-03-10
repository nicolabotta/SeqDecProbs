This repository contains the Idris code referred to in "SDPs, dependent
types and generic solutions". The manuscript has been submitted to LMCS
in August 2014 and is currently under review.

Since 2014, both our framework for specifying sequential decision
problems and computing provably optimal policy sequences and Idris
itself have evolved quite a lot. You can find the most recent version of
the framework in frameworks/14-.

We try to make the code in this repository compilable with the current
Idris version. This should allow reviewers to easily check the results
presented in our manuscript. But it also means that we have to modify
and maintain the code as Idris evolves.

Thus, for instance, we had to rename Sigma types to comply with changes
indroduced with Idris version 0.10. We have checked that the examples
discussed in the manuscript

* DynamicProgramming/S1206_CylinderExample1.lidr
* DynamicProgramming/S1206_CylinderExample4.lidr

type check and compile with Idris version 0.10.2-git:504187b. With this
Idris version, you should be able to compile the examples by just typing
"make cylinder1" and "make cylinder4" from the command line.

Running cylinder1.exe ...

The cylinder4 example is mainly meant to illustrate how dependent types
can be used to prevent attempts at computing optimal sequences of
controls of length n for initial states from which one cannot actually
perform n decision steps. Such attempts should be detected by the type
checker and rejected.

You can see that this is actually the case by first compiling the
cylinder4 example. In this example, we compute an optimal sequence of
controls for 4 steps for a decision problem similar to the one
illustrated in Figure 2 of the manuscript. If the initial state is "b"
as defined at line 352 of DynamicProgramming/S1206_CylinderExample4.lidr

```
> x0 = ((1 ** LTESucc (LTESucc LTEZero)) ** Oh)
```

the program type checks and compiles. Running the code
(DynamicProgramming/cylinder4.exe from the command line) should yield

[R, R, R, A]

which is interpreted as three moves to the right (from "b" to "e") and
one ahead. In contrast, if one attempts at computing an optimal sequence
of controls for 4 decision steps starting from "a" by replacing line 352
with

```
> x0 = ((0 ** LTESucc LTEZero) ** Oh)
```

the type checker should detect that "a" is not viable for 4 steps and
the program should fail to compile with:

```
Type checking ./DynamicProgramming/S1206_CylinderExample4.lidr
./DynamicProgramming/S1206_CylinderExample4.lidr:359:6-8:
When checking right hand side of v0 with expected type
        So (viable nSteps x0)

Type mismatch between
        So True (Type of Oh)
and
        So False (Expected type)

Specifically:
        Type mismatch between
                True
        and
                False
Makefile:20: recipe for target 'cylinder4' failed
make: *** [cylinder4] Error 1
```
