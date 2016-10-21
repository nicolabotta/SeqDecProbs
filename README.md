# Sequential Decision Problems

This repository contains Idris code supporting the computation of
Sequential Decision Problems (SDPs). The ongoing research is also
documented in some research papers (see below).

Some related Agda code is available in
[patrikja/SeqDecProb_Agda](https://github.com/patrikja/SeqDecProb_Agda).

## Idris source code

* [manuscripts/](manuscripts/)
    * 2014.LMCS: code from the paper "SDPs, dependent types and generic solutions". [The simple "cylinder" example](manuscripts/2014.LMCS/code/DynamicProgramming/S1206_CylinderExample1.lidr).
    * 2015.JFP: code from the paper "Contributions to a computational theory of policy advice and avoidability". [A fairly self-contained file with the core development](manuscripts/2015.JFP/code/monadic.lidr), [some more code from the paper sections](manuscripts/2015.JFP/code/). The code is a snapshot matching the paper when submitted. (The full [support framework](frameworks/14-/) keeps developing.)
* [frameworks/](frameworks/)
    Supporting code for the papers - Years [2011-2014](frameworks/11-14/) and a reworked structure from [2014-](frameworks/14-/).
* [issue_reports/](issue_reports/)
    The development of this code base has resulted in quite a few issue reports for the Idris implementation.
* Some other directories: [talks/](talks/), [idris-lang/](idris-lang/), [notes/](notes/), [prototypes/](prototypes/), ...

## Research papers

### 2013: SDPs, dependently-typed solutions

Title: Sequential decision problems, dependently-typed solutions.

Authors: [Nicola Botta](https://www.pik-potsdam.de/members/botta/publications), Cezar Ionescu, and Edwin Brady.

Paper: http://ceur-ws.org/Vol-1010/paper-06.pdf

Published in Proceedings of the Conferences on Intelligent Computer
  Mathematics (CICM 2013), "Programming Languages for Mechanized Mathematics
  Systems Workshop (PLMMS)", volume 1010 of CEUR Workshop Proceedings, 2013.

### 2014: SDPs, dependent types and generic solutions (in submission)

Title: Sequential decision problems, dependent types and generic solutions

* 2014-08: Submitted for publication
* 2015-06: Received referee reports
* 2015-07: [Resubmitted](http://www.cse.chalmers.se/~patrikj/papers/SeqDecProbDepType_LMCS_2015_preprint.pdf).
* 2015-12: Received 2nd round of referee reports
* 2016-02: [Resubmitted](http://www.cse.chalmers.se/~patrikj/papers/SeqDecProbDepType_LMCS_2016_preprint.pdf).
* 2016-07: Received 3rd round of referee reports ("Accept with minor revision")
* 2016-08: [Resubmitted](http://www.cse.chalmers.se/~patrikj/papers/SeqDecProbDepType_LMCS_2016-08_preprint.pdf).
* 2016-10: Accepted for publication in LICS (as is).

Authors: Nicola Botta, Patrik Jansson, Cezar Ionescu, David R. Christiansen, Edwin Brady

### 2015: Contributions to a computational theory of policy advice and avoidability

Authors: Nicola Botta, Patrik Jansson, Cezar Ionescu

* 2016-01-06: Submitted to the Journal of Functional Programming (JFP) Special issue on Dependently Typed Programming. (JFP is a [RoMEO Green journal](http://www.sherpa.ac.uk/romeo/search.php?issn=0956-7968).)
* [Full text pre-print available](http://www.cse.chalmers.se/~patrikj/papers/CompTheoryPolicyAdviceAvoidability_JFP_2016_preprint.pdf)
* 2016-07: Review verdict: "Reject and resubmit"

The work was partially supported by the
[GRACeFUL project](https://www.graceful-project.eu/)
(640954, from the call H2020-FETPROACT-2014) and by the
[CoeGSS project](http://coegss.eu/)
(676547, H2020-EINFRA-2015-1) in the context of
Global Systems Science (GSS).
