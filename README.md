# Sequential Decision Problems

This repository contains Idris code supporting the computation of
Sequential Decision Problems (SDPs). The ongoing research is also
resulting in some research papers (see below).

Some related Agda code is available in
[patrikja/SeqDecProb_Agda](https://github.com/patrikja/SeqDecProb_Agda).

## Idris source code

* [manuscripts](manuscripts/)
    * 2014.LMCS: code from the paper "SDPs, dependent types and generic solutions". [The simple "cylinder" example](manuscripts/2014.LMCS/code/DynamicProgramming/S1206_CylinderExample1.lidr).
    * 2015.MSS: code from the paper "A computational theory of policy advice and avoidability". [A fairly self-contained file](manuscripts/2015.MSS/code/monadic.lidr) and [the support framework](frameworks/14-/).
* [frameworks](frameworks/)
    Supporting code for the papers - Years [2011-2014](frameworks/11-14/) and a reworked structure from [2014-](frameworks/14-/).
* [issue_reports](issue_reports/)
    The development of this code base has resulted in quite a few issue reports for the Idris implementation.
* Some other directories: [talks](talks/), [idris-lang](idris-lang/), [notes](notes/), [prototypes](prototypes/), ...

## Research papers

### 2013: SDPs, dependently-typed solutions

Title: Sequential decision problems, dependently-typed solutions.

Authors: Nicola Botta, Cezar Ionescu, and Edwin Brady.

Published in Proceedings of the Conferences on Intelligent Computer
  Mathematics (CICM 2013), "Programming Languages for Mechanized Mathematics
  Systems Workshop (PLMMS)", volume 1010 of CEUR Workshop Proceedings, 2013

### 2014: SDPs, dependent types and generic solutions (in submission)

Title: Sequential decision problems, dependent types and generic solutions

Submitted for publication 2014-08, referee reports 2015-06. Resubmitted 2015-07.

Authors: Nicola Botta, Patrik Jansson, Cezar Ionescu, David R. Christiansen, Edwin Brady

### 2015: A computational theory of policy advice and avoidability

Authors: Nicola Botta, Patrik Jansson, Cezar Ionescu

In submission.
