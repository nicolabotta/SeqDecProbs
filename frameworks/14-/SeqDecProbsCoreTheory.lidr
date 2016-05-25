> module SeqDecProbsCoreTheory

> import SeqDecProbsCoreAssumptions

> -- import NatProperties
> import Sigma
> import SigmaOperations

> %default total
> %access public export
> %auto_implicits off


* The theory of monadic sequential decision problems (SDP):


** Policies and policy sequences

Policies are just functions that associate to every state |x| at
decision step |t| which is reachable and viable for |S m| steps (from
which |S m| more decision steps are doable) a "good" control, see
"SeqDecProbsCoreAssumptions":

> Policy : (t : Nat) -> (n : Nat) -> Type
> Policy t Z      =  ()
> Policy t (S m)  =  (x : State t) -> Reachable x -> Viable (S m) x -> GoodCtrl t x m

A policy sequence for making |n| decision steps starting from some
(reachable, viable for |n| steps) state at decision step |t| is just a
list of policies of length |n|, one for each decision step:

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  {t : Nat} -> 
>            PolicySeq t Z
>   (::)  :  {t : Nat} -> {n : Nat} -> 
>            Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)


** The value of policy sequences

Measuring the value (in terms of possible sums of rewards) of making |n|
decision steps with a given policy sequence |ps : PolicySeq t n| from a
(reachable, viable for |n| steps) state |x : State t|

<   val : {t : Nat} -> {n : Nat} -> 
<         (x : State t) -> Reachable x -> Viable n x -> PolicySeq t n -> Val

is not trivial. If |n = Z| (and |ps = Nil|) we are not making any
decision step. Thus, we do not collect any reward and the value is just zero:

<   val {t} {n = Z} x r v ps = zero

If |n = S m| and |ps| consists of a policy |p : Policy t (S m)| and of a
policy sequence |ps : PolicySeq (S t) m|, things are more complicated:

<   val {t} {n = S m} x r v (p :: ps) = ?

Here, we first have to compute the rewards obtained by selecting the
control |y = ctrl (p x r v)| in the first decision step. We get one
possible reward for each state in |step t x y|. Thus, if |x' `Elem`
(step t x y)|, its corresponding reward is

< reward t x y x'

Next, we have to add to all these rewards (one for every |x'|) the
values of making |m| further decision steps with |ps| starting from
|x'|:

< val x' r' v' ps

To do so, we have to provide reachability and viability evidences |r'|
and |v'| for |x'|. Finally, we have to reduce all possible values to a
single aggregated value with the decision-maker specific measure |meas|.

It is useful to introduce the set of possible states that can be
obtained by selecting the control |y : Ctrl t x| in |x : State t|:

> PossibleState : {t : Nat} -> 
>                 (x  : State t) -> (y : Ctrl t x) -> Type
> PossibleState {t} x y = Sigma (State (S t)) (\ x' => x' `Elem` (step t x y))

With this notion in place and assuming 

<   val : {t : Nat} -> {n : Nat} -> 
<         (x : State t) -> Reachable x -> Viable n x -> PolicySeq t n -> Val

to be available, we can easily implement

> mutual

>   sval : {t : Nat} -> {m : Nat} -> 
>          (x  : State t) -> (r  : Reachable x) -> (v  : Viable (S m) x) ->
>          (gy  : GoodCtrl t x m) -> (ps : PolicySeq (S t) m) ->
>          PossibleState x (ctrl gy) -> Val
>   sval {t} {m} x r v gy ps (MkSigma x' x'estep) = reward t x y x' `plus` val x' r' v' ps where
>     y   : Ctrl t x
>     y   = ctrl gy
>     ar' : All Reachable (step t x y)
>     ar' = reachableSpec1 x r y
>     av' : All (Viable m) (step t x y)
>     av' = allViable {y} gy
>     r'  : Reachable x'
>     r'  = containerMonadSpec3 x' (step t x y) ar' x'estep
>     v'  : Viable m x'
>     v'  = containerMonadSpec3 x' (step t x y) av' x'estep

And finally

>   val : {t : Nat} -> {n : Nat} -> 
>         (x : State t) -> Reachable x -> Viable n x -> PolicySeq t n -> Val
>   val {t} {n = Z} x r v ps = zero
>   val {t} {n = S m} x r v (p :: ps) = meas (fmap (sval x r v gy ps) (tagElem mx')) where
>     gy   :  GoodCtrl t x m
>     gy   =  p x r v
>     y    : Ctrl t x
>     y    = ctrl gy
>     mx'  :  M (State (S t))
>     mx'  =  step t x y


**  Optimality of policy sequences:

> |||
> OptPolicySeq : {t : Nat} -> {n : Nat} -> 
>                PolicySeq t n -> Type
> OptPolicySeq {t} {n} ps  =  (ps' : PolicySeq t n) ->
>                             (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>                             (val x r v ps') `LTE` (val x r v ps)

Policy sequences of length zero are optimal

> |||
> nilOptPolicySeq : OptPolicySeq Nil
> nilOptPolicySeq ps' x r v = reflexiveLTE zero


** Optimal extensions of policy sequences:

> |||
> OptExt : {t : Nat} -> {m : Nat} -> 
>          PolicySeq (S t) m -> Policy t (S m) -> Type
> OptExt {t} {m} ps p  =  (p' : Policy t (S m)) ->
>                         (x : State t) -> (r : Reachable x) -> (v : Viable (S m) x) ->
>                         (val x r v (p' :: ps)) `LTE` (val x r v (p :: ps))


** Bellman's principle of optimality:

> |||
> Bellman : {t : Nat} -> {m : Nat} -> 
>           (ps  : PolicySeq (S t) m)  ->   OptPolicySeq ps ->
>           (p   : Policy t (S m))     ->   OptExt ps p ->
>           OptPolicySeq (p :: ps)

> Bellman {t} {m} ps ops p oep = opps where
>   opps : OptPolicySeq (p :: ps)
>   opps (p' :: ps') x r v = transitiveLTE (val x r v (p' :: ps')) 
>                                          (val x r v (p' :: ps)) 
>                                          (val x r v (p :: ps)) 
>                                          s4 s5 where
>     gy' : GoodCtrl t x m
>     gy' = p' x r v                       
>     y'  : Ctrl t x
>     y'  = ctrl gy'
>     mx' : M (State (S t))
>     mx' = step t x y'
>     av' : All (Viable m) mx'
>     av' = allViable {y = y'} gy'
>     f' : PossibleState x (ctrl gy') -> Val
>     f' = sval x r v gy' ps'
>     f  : PossibleState x (ctrl gy') -> Val
>     f  = sval x r v gy' ps
>     s1 : (x' : State (S t)) -> (r' : Reachable x') -> (v' : Viable m x') ->
>          (val x' r' v' ps') `LTE` (val x' r' v' ps)
>     s1 x' r' v' = ops ps' x' r' v'
>     s2 : (z : PossibleState x (ctrl gy')) -> (f' z) `LTE` (f z)
>     s2 (MkSigma x' x'emx') = 
>       monotonePlusLTE (reflexiveLTE (reward t x y' x')) (s1 x' r' v') where 
>         ar' : All Reachable mx'
>         ar' = reachableSpec1 x r y'
>         r'  : Reachable x'
>         r'  = containerMonadSpec3 x' mx' ar' x'emx'
>         v'  : Viable m x'
>         v'  = containerMonadSpec3 x' mx' av' x'emx'
>     s3 : (meas (fmap f' (tagElem mx'))) `LTE` (meas (fmap f (tagElem mx')))
>     s3 = measMon f' f s2 (tagElem mx')
>     s4 : (val x r v (p' :: ps')) `LTE` (val x r v (p' :: ps))
>     s4 = s3
>     s5 : (val x r v (p' :: ps)) `LTE` (val x r v (p :: ps))
>     s5 = oep p' x r v


** Optimal extensions

> ||| 
> cval : {t : Nat} -> {n : Nat} ->
>        (x  : State t) ->
>        (r  : Reachable x) ->
>        (v  : Viable (S n) x) ->
>        (ps : PolicySeq (S t) n) ->
>        GoodCtrl t x n -> Val
> cval {t} x r v ps gy = meas (fmap (sval x r v gy ps) (tagElem mx')) where
>   y    : Ctrl t x
>   y    = ctrl gy
>   mx'  :  M (State (S t))
>   mx'  =  step t x y


> ||| 
> optExt : {t : Nat} -> {n : Nat} -> 
>          PolicySeq (S t) n -> Policy t (S n)
> optExt {t} {n} ps = p where
>   p : Policy t (S n)
>   p x r v = argmax x v (cval x r v ps)


> |||
> optExtLemma : {t : Nat} -> {n : Nat} -> 
>               (ps : PolicySeq (S t) n) -> OptExt ps (optExt ps)
> optExtLemma {t} {n} ps p' x r v = s2 where
>   p     :  Policy t (S n)
>   p     =  optExt ps
>   gy    :  GoodCtrl t x n
>   gy    =  p x r v
>   y     :  Ctrl t x
>   y     =  ctrl gy
>   av    :  All (Viable n) (step t x y)
>   av    =  allViable {y = y} gy
>   gy'   :  GoodCtrl t x n
>   gy'   =  p' x r v
>   y'    :  Ctrl t x
>   y'    =  ctrl gy'
>   av'   :  All (Viable n) (step t x y')
>   av'   =  allViable {y = y'} gy'
>   g     :  GoodCtrl t x n -> Val
>   g     =  cval x r v ps
>   f     :  PossibleState x (ctrl gy) -> Val
>   f     =  sval x r v gy ps
>   f'    :  PossibleState x (ctrl gy') -> Val
>   f'    =  sval x r v gy' ps
>   s1    :  (g gy') `LTE` (max x v g)
>   s1    =  maxSpec x v g gy'
>   s2    :  (g gy') `LTE` (g (argmax x v g))
>   s2    =  replace {P = \ z => (g gy' `LTE` z)} (argmaxSpec x v g) s1
>   -- the rest of the steps are for the (sort of) human reader
>   s3    :  (g gy') `LTE` (g gy)
>   s3    =  s2
>   s4    :  (cval x r v ps gy') `LTE` (cval x r v ps gy)
>   s4    =  s3
>   s5    :  (meas (fmap f' (tagElem (step t x y')))) `LTE` (meas (fmap f (tagElem (step t x y))))
>   s5    =  s4
>   s6    :  (val x r v (p' :: ps)) `LTE` (val x r v (p :: ps))
>   s6    =  s5

** Generic machine checkable backwards induction

> bi : (t : Nat) -> (n : Nat) -> PolicySeq t n
> bi t  Z     =  Nil
> bi t (S n)  =  optExt ps :: ps where
>   ps : PolicySeq (S t) n
>   ps = bi (S t) n
> {-
> bi t (S n)  =  let ps = bi (S t) n
>                in (optExt ps :: ps)
> -}


> biLemma : (t : Nat) -> (n : Nat) -> OptPolicySeq (bi t n)
> biLemma t  Z     =  nilOptPolicySeq
> biLemma t (S n)  =  Bellman ps ops p oep where
>   ps   :  PolicySeq (S t) n
>   ps   =  bi (S t) n
>   ops  :  OptPolicySeq ps
>   ops  =  biLemma (S t) n
>   p    :  Policy t (S n)
>   p    =  optExt ps
>   oep  :  OptExt ps p
>   oep  =  optExtLemma ps


Thus, we can compute provably optimal sequences of policies for
arbitrary SDPs and number of decision steps. 


> {-

> ---}
