> module SeqDecProbsCoreTheory

> import SeqDecProbsCoreAssumptions

> import NatProperties
> import Sigma
> import SigmaOperations

> %default total
> %access public export
> %auto_implicits off


* The theory of monadic sequential decision problems (SDP):


** Policies and policy sequences

> Policy : (t : Nat) -> (n : Nat) -> Type
> Policy t Z      =  ()
> Policy t (S m)  =  (x : State t) -> Reachable x -> Viable (S m) x -> 
>                    Sigma (Ctrl t x) (\ y => All (Viable m) (step t x y))

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  {t : Nat} -> 
>            PolicySeq t Z
>   (::)  :  {t : Nat} -> {n : Nat} -> 
>            Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)


** The value of policy sequences

> mutual

>   mkf : {t : Nat} -> {m : Nat} -> 
>         (x  : State t) -> (r  : Reachable x) -> (v  : Viable (S m) x) ->
>         (y  : Ctrl t x) -> (av : All (Viable m) (step t x y)) ->
>         (ps : PolicySeq (S t) m) ->
>         Sigma (State (S t)) (\ x' => x' `Elem` (step t x y)) -> Nat
>   mkf {t} {m} x r v y av ps (MkSigma x' x'estep) = reward t x y x' + val x' r' v' ps where
>     ar : All Reachable (step t x y)
>     ar = reachableSpec1 x r y
>     r' : Reachable x'
>     r' = containerMonadSpec3 x' (step t x y) ar x'estep
>     v' : Viable m x'
>     v' = containerMonadSpec3 x' (step t x y) av x'estep

>   val : {t : Nat} -> {n : Nat} -> 
>         (x : State t) -> Reachable x -> Viable n x -> PolicySeq t n -> Nat
>   val {t} {n = Z} x r v ps = Z
>   val {t} {n = S m} x r v (p :: ps) = meas (fmap f (tagElem mx')) where
>     y    :  Ctrl t x
>     y    =  outl (p x r v)
>     mx'  :  M (State (S t))
>     mx'  =  step t x y
>     av   :  All (Viable m) mx'
>     av   =  outr (p x r v)
>     f    :  Sigma (State (S t)) (\ x' => x' `Elem` mx') -> Nat
>     f    =  mkf x r v y av ps


**  Optimality of policy sequences:

> OptPolicySeq : {t : Nat} -> {n : Nat} -> 
>                PolicySeq t n -> Type
> OptPolicySeq {t} {n} ps  =  (ps' : PolicySeq t n) ->
>                             (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>                             (val x r v ps') `LTE` (val x r v ps)

Policy sequences of length zero are optimal

> nilOptPolicySeq : OptPolicySeq Nil
> nilOptPolicySeq ps' x r v = reflexiveLTE Z


** Optimal extensions of policy sequences:

> OptExt : {t : Nat} -> {m : Nat} -> 
>          PolicySeq (S t) m -> Policy t (S m) -> Type
> OptExt {t} {m} ps p  =  (p' : Policy t (S m)) ->
>                         (x : State t) -> (r : Reachable x) -> (v : Viable (S m) x) ->
>                         (val x r v (p' :: ps)) `LTE` (val x r v (p :: ps))


** Bellman's principle of optimality:

> Bellman : {t : Nat} -> {m : Nat} -> 
>           (ps  : PolicySeq (S t) m)  ->   OptPolicySeq ps ->
>           (p   : Policy t (S m))     ->   OptExt ps p ->
>           OptPolicySeq (p :: ps)

> Bellman {t} {m} ps ops p oep = opps where
>   opps : OptPolicySeq (p :: ps)
>   opps (p' :: ps') x r v = transitiveLTE
>                            (val x r v (p' :: ps'))
>                            (val x r v (p' :: ps))
>                            (val x r v (p :: ps))
>                            s4 s5 where
>     y' : Ctrl t x
>     y' = outl (p' x r v)
>     mx' : M (State (S t))
>     mx' = step t x y'
>     av' : All (Viable m) mx'
>     av' = outr (p' x r v)
>     f' : Sigma (State (S t)) (\ x' => x' `Elem` mx') -> Nat
>     f' = mkf x r v y' av' ps'
>     f  : Sigma (State (S t)) (\ x' => x' `Elem` mx') -> Nat
>     f  = mkf x r v y' av' ps
>     s1 : (x' : State (S t)) -> (r' : Reachable x') -> (v' : Viable m x') ->
>          (val x' r' v' ps') `LTE` (val x' r' v' ps)
>     s1 x' r' v' = ops ps' x' r' v'
>     s2 : (z : Sigma (State (S t)) (\ x' => x' `Elem` mx')) -> (f' z) `LTE` (f z)
>     s2 (MkSigma x' x'emx') = 
>       monotoneNatPlusLTE lteRefl (s1 x' r' v') where 
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

> mkg : {t : Nat} -> {n : Nat} ->
>       (x  : State t) ->
>       (r  : Reachable x) ->
>       (v  : Viable (S n) x) ->
>       (ps : PolicySeq (S t) n) ->
>       Sigma (Ctrl t x) (\ y => All (Viable n) (step t x y)) -> Nat
> mkg {t} x r v ps yav = meas (fmap f (tagElem (step t x (outl yav)))) where
>   f : Sigma (State (S t)) (\ x' => x' `Elem` (step t x (outl yav))) -> Nat
>   f = mkf x r v (outl yav) (outr yav) ps

> optExt : {t : Nat} -> {n : Nat} -> 
>          PolicySeq (S t) n -> Policy t (S n)
> optExt {t} {n} ps = p where
>   p : Policy t (S n)
>   p x r v = argmax x v g where
>     g : Sigma (Ctrl t x) (\ y => All (Viable n) (step t x y)) -> Nat
>     g = mkg x r v ps

> optExtLemma : {t : Nat} -> {n : Nat} -> 
>               (ps : PolicySeq (S t) n) -> OptExt ps (optExt ps)
> optExtLemma {t} {n} ps p' x r v = s2 where
>   p     :  Policy t (S n)
>   p     =  optExt ps
>   yav   :  Sigma (Ctrl t x) (\ z => All (Viable n) (step t x z))
>   yav   =  p x r v
>   y     :  Ctrl t x
>   y     =  outl yav
>   av    :  All (Viable n) (step t x y)
>   av    =  outr yav
>   yav'  :  Sigma (Ctrl t x) (\ z => All (Viable n) (step t x z))
>   yav'  =  p' x r v
>   y'    :  Ctrl t x
>   y'    =  outl yav'
>   av'   :  All (Viable n) (step t x y')
>   av'   =  outr yav'
>   g     :  Sigma (Ctrl t x) (\ z => All (Viable n) (step t x z)) -> Nat
>   g     =  mkg x r v ps
>   f     :  Sigma (State (S t)) (\ x' => x' `Elem` (step t x y)) -> Nat
>   f     =  mkf x r v y av ps
>   f'    :  Sigma (State (S t)) (\ x' => x' `Elem` (step t x y')) -> Nat
>   f'    =  mkf x r v y' av' ps
>   s1    :  (g yav') `LTE` (max x v g)
>   s1    =  maxSpec t x v g yav'
>   s2    :  (g yav') `LTE` (g (argmax x v g))
>   s2    =  replace {P = \ z => (g yav' `LTE` z)} (argmaxSpec t x v g) s1
>   -- the rest of the steps are for the human reader
>   s3    :  (g yav') `LTE` (g yav)
>   s3    =  s2
>   s4    :  (mkg x r v ps yav') `LTE` (mkg x r v ps yav)
>   s4    =  s3
>   s5    :  (meas (fmap f' (tagElem (step t x y')))) `LTE` (meas (fmap f (tagElem (step t x y))))
>   s5    =  s4
>   s6    :  (val x r v (p' :: ps)) `LTE` (val x r v (p :: ps))
>   s6    =  s5


** Generic machine checkable backwards induction

> bi : (t : Nat) -> (n : Nat) -> PolicySeq t n
> bi t  Z     =  Nil
> bi t (S n)  =  let -- ps : PolicySeq (S t) n
>                    ps = bi (S t) n
>                in (optExt ps :: ps)

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
