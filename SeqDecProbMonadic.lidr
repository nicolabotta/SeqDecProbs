> module SeqDecProbMonadic

> import Data.So
> import Data.Fin
> import Control.Isomorphism

> import Prop
> import NatProperties
> import SigmaOperations
> import RelSyntax
> import RelFloatPostulates

 
> %default total 


The theory of monadic sequential decision problems (SDP):


A SDP is specified in terms of a monad ...

> M : Type -> Type

> fmap : {A, B : Type} -> (A -> B) -> M A -> M B
> -- unused functorSpec1 : fmap . id = id
> -- unused functorSpec2 : fmap (f . g) = (fmap f) . (fmap g)

> ret   :  {A : Type} -> A -> M A
> bind  :  {A, B : Type} -> M A -> (A -> M B) -> M B
> -- unused monadSpec1   :  (fmap f) . ret = ret . f
> -- unused monadSpec21  :  bind (ret a) f = f a
> -- unused monadSpec22  :  bind ma ret = ma
> -- unused monadSpec23  :  {A, B, C : Type} -> {f : A -> M B} -> {g : B -> M C} -> 
> --                        bind (bind ma f) g = bind ma (\ a => bind (f a) g)

> join  :  {A : Type} -> M (M A) -> M A
> join mma = bind mma id

... which is required to be a "container" monad:

> Elem     :  {A : Type} -> A -> M A -> Prop
> All      :  {A : Type} -> (P : A -> Prop) -> M A -> Prop
> All {A} P ma = (a : A) -> a `Elem` ma -> P a
> tagElem  :  {A : Type} -> (ma : M A) -> M (a : A ** a `Elem` ma)

The standard examples are |M = Id| (deterministic SDP), |M = List|
(non-deterministic SDP) and |M = Prob| (stochastic SDP). 

The decision problem itself is specified by giving the decision
process ...

> X       : (t : Nat) -> Type

> Y       : (t : Nat) -> (x : X t) -> Type

> step    : (t : Nat) -> (x : X t) -> (y : Y t x) -> M (X (S t))

> reward  : (t : Nat) -> (x : X t) -> (y : Y t x) -> (x' : X (S t)) -> Float

> rewards : (t : Nat) -> (x : X t) -> (y : Y t x) -> M Float
> rewards t x y = fmap (reward t x y) (step t x y)

... and a measure:

> meas : M Float -> Float
> measMon  :  {A : Type} -> 
>             (f : A -> Float) -> (g : A -> Float) -> 
>             ((a : A) -> So (f a <= g a)) ->
>             (ma : M A) -> So (meas (fmap f ma) <= meas (fmap g ma))

For every SDP, we can build the following notions:


  Equivalent problem

> MX : (t : Nat) -> Type
> MX t = M (X t)

> mstep : (t : Nat) -> (mx : MX t) -> (p : ((x : X t) -> Y t x)) -> MX (S t)
> mstep t mx p = join (fmap (\ x => step t x (p x)) mx)


  Viability and reachability:

> Pred : X t -> X (S t) -> Prop
> Pred {t} x x'  =  Exists (\ y => x' `Elem` step t x y)

> Viable : (n : Nat) -> X t -> Prop
> Viable {t}  Z    _  =  ()
> Viable {t} (S m) x  =  Exists (\ y => All (Viable m) (step t x y))

> Reachable : X t' -> Prop
> Reachable {t' =   Z} _   =  ()
> Reachable {t' = S t} x'  =  Exists (\ x => (Reachable x, x `Pred` x'))


  Refined policies:

> Policy : (t : Nat) -> (n : Nat) -> Type
> Policy t Z      =  ()
> Policy t (S m)  =  (x : X t) -> Reachable x -> Viable (S m) x -> (y : Y t x ** All (Viable m) (step t x y))

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  PolicySeq t Z
>   (::)  :  Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)


  Value of (refined) policy sequences:

> mutual

>   mkf : (x  : X t) ->
>         (r  : Reachable x) ->
>         (v  : Viable (S m) x) -> 
>         (y  : Y t x) ->
>         (av : All (Viable m) (step t x y)) ->
>         (ps : PolicySeq (S t) m) ->
>         (x' : X (S t) ** x' `Elem` (step t x y)) -> Float
>   mkf {t} {m} x r v y av ps (x' ** x'estep) = reward t x y x' + val x' r' v' ps where
>     xpx' : x `Pred` x'
>     xpx' = Evidence y x'estep
>     r' : Reachable x'
>     r' = Evidence x (r , xpx')
>     v' : Viable m x'
>     v' = av x' x'estep

>   val : (x : X t) -> Reachable x -> Viable n x -> PolicySeq t n -> Float
>   val {t} {n = Z} x r v ps = 0
>   val {t} {n = S m} x r v (p :: ps) = meas (fmap f (tagElem mx')) where
>     y    :  Y t x
>     y    =  outl (p x r v)
>     mx'  :  M (X (S t))
>     mx'  =  step t x y
>     av   :  All (Viable m) mx'
>     av   =  outr (p x r v)
>     f    :  (x' : X (S t) ** x' `Elem` mx') -> Float
>     f    =  mkf x r v y av ps


  Optimality of policy sequences:

> OptPolicySeq : PolicySeq t n -> Prop
> OptPolicySeq {t} {n} ps  =  (ps' : PolicySeq t n) -> 
>                             (x : X t) ->
>                             (r : Reachable x) ->
>                             (v : Viable n x) ->
>                             So (val x r v ps' <= val x r v ps)

> nilOptPolicySeq : OptPolicySeq Nil
> nilOptPolicySeq ps' x r v = reflexiveFloatLTE 0


  Optimal extensions of policy sequences:

> OptExt : PolicySeq (S t) m -> Policy t (S m) -> Prop
> OptExt {t} {m} ps p  =  (p' : Policy t (S m)) ->
>                         (x : X t) ->
>                         (r : Reachable x) -> 
>                         (v : Viable (S m) x) -> 
>                         So (val x r v (p' :: ps) <= val x r v (p :: ps))

  
  Bellman's principle of optimality:

> Bellman  :  (ps : PolicySeq (S t) m) ->
>             OptPolicySeq ps ->
>             (p : Policy t (S m)) ->
>             OptExt ps p ->
>             OptPolicySeq (p :: ps)

> Bellman {t} {m} ps ops p oep = opps where
>   opps : OptPolicySeq (p :: ps)
>   opps (p' :: ps') x r v = transitiveFloatLTE s4 s5 where
>     y' : Y t x
>     y' = outl (p' x r v)
>     mx' : M (X (S t))
>     mx' = step t x y'
>     av' : All (Viable m) mx'
>     av' = outr (p' x r v)    
>     f' : (x' : X (S t) ** x' `Elem` mx') -> Float
>     f' = mkf x r v y' av' ps'
>     f  : (x' : X (S t) ** x' `Elem` mx') -> Float
>     f  = mkf x r v y' av' ps
>     s1 : (x' : X (S t)) -> (r' : Reachable x') -> (v' : Viable m x') ->
>          So (val x' r' v' ps' <= val x' r' v' ps)
>     s1 x' r' v' = ops ps' x' r' v'
>     s2 : (z : (x' : X (S t) ** x' `Elem` mx')) -> So (f' z <= f z)
>     s2 (x' ** x'emx') = monotoneFloatPlusLTE (reward t x y' x') (s1 x' r' v') where
>       xpx' : x `Pred` x'
>       xpx' = Evidence y' x'emx'
>       r' : Reachable x'
>       r' = Evidence x (r , xpx')
>       v' : Viable m x'
>       v' = av' x' x'emx'
>     s3 : So (meas (fmap f' (tagElem mx')) <= meas (fmap f (tagElem mx')))
>     s3 = measMon f' f s2 (tagElem mx')
>     s4 : So (val x r v (p' :: ps') <= val x r v (p' :: ps))
>     s4 = s3
>     s5 : So (val x r v (p' :: ps) <= val x r v (p :: ps))
>     s5 = oep p' x r v


The idea is that, if clients can implement max and argmax

> max    : (t : Nat) -> (x : X t) -> Viable (S n) x ->
>          (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Float) -> 
>          Float
> argmax : (t : Nat) -> (x : X t) -> Viable (S n) x ->
>          (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Float) -> 
>          Sigma (Y t x) (\ y => All (Viable n) (step t x y))

that fulfill the specification

> typeHelper : (t : Nat) -> (x : X t) -> Viable (S n) x ->
>              (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Float) -> 
>              Type
> typeHelper t x v f = SeqDecProbMonadic.max t x v f = f (SeqDecProbMonadic.argmax t x v f)

> maxSpec     :  (t : Nat) -> (x : X t) -> Viable (S n) x ->
>                (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Float) -> 
>                (s : (y : Y t x ** All (Viable n) (step t x y))) -> 
>                So (f s <= SeqDecProbMonadic.max t x v f)
> argmaxSpec  :  (t : Nat) -> (x : X t) -> Viable (S n) x ->
>                (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Float) -> 
>                typeHelper t x v f -- SeqDecProbMonadic.max t x v f = f (SeqDecProbMonadic.argmax t x v f)

then we can implement a function that computes machine chackable optimal
extensions for arbitrary policy sequences:

> mkg : (x  : X t) ->
>       (r  : Reachable x) ->
>       (v  : Viable (S n) x) -> 
>       (ps : PolicySeq (S t) n) ->
>       (y : Y t x ** All (Viable n) (step t x y)) -> Float
> mkg {t} {n} x r v ps yav = meas (fmap f (tagElem (step t x (outl yav)))) where
>   f : (x' : X (S t) ** x' `Elem` (step t x (outl yav))) -> Float
>   f = mkf x r v (outl yav) (outr yav) ps

> optExt : PolicySeq (S t) n -> Policy t (S n)
> optExt {t} {n} ps = p where
>   p : Policy t (S n)
>   p x r v = argmax t x v g where
>     g : (y : Y t x ** All (Viable n) (step t x y)) -> Float
>     g = mkg x r v ps

> optExtLemma : (ps : PolicySeq (S t) n) -> OptExt ps (optExt ps)
> optExtLemma {t} {n} ps p' x r v = s2 where
>   p     :  Policy t (S n)
>   p     =  optExt ps
>   yav   :  (y : Y t x ** All (Viable n) (step t x y))
>   yav   =  p x r v
>   y     :  Y t x
>   y     =  outl yav
>   av    :  All (Viable n) (step t x y) 
>   av    =  outr yav
>   yav'  :  (y : Y t x ** All (Viable n) (step t x y))
>   yav'  =  p' x r v
>   y'    :  Y t x
>   y'    =  outl yav'
>   av'   :  All (Viable n) (step t x y')
>   av'   =  outr yav'
>   g     :  (y : Y t x ** All (Viable n) (step t x y)) -> Float
>   g     =  mkg x r v ps
>   f     :  (x' : X (S t) ** x' `Elem` (step t x y)) -> Float
>   f     =  mkf x r v y av ps        
>   f'    :  (x' : X (S t) ** x' `Elem` (step t x y')) -> Float
>   f'    =  mkf x r v y' av' ps        
>   s1    :  So (g yav' <= SeqDecProbMonadic.max t x v g)
>   s1    =  maxSpec t x v g yav'
>   s2    :  So (g yav' <= g (argmax t x v g))
>   s2    =  replace {P = \ z => So (g yav' <= z)} (argmaxSpec t x v g) s1
>   -- the rest of the steps are for the human reader
>   s3    :  So (g yav' <= g yav)
>   s3    =  s2
>   s4    :  So (mkg x r v ps yav' <=  mkg x r v ps yav)
>   s4    =  s3
>   s5    :  So (meas (fmap f' (tagElem (step t x y'))) <= meas (fmap f (tagElem (step t x y))))
>   s5    =  s4          
>   s6    :  So (val x r v (p' :: ps) <= val x r v (p :: ps))
>   s6    =  s5


With |optExt|, it is easy to implement a generic machine checkable backwards
induction:

> bi : (t : Nat) -> (n : Nat) -> PolicySeq t n
> bi t  Z     =  Nil
> bi t (S n)  =  (optExt ps :: ps) where
>   ps : PolicySeq (S t) n
>   ps = bi (S t) n

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


that is, we can compute provably optimal sequences of policies for
arbitrary SDPs and number of decision steps. The theory can provide
additional support to policy advice, e.g., with methods to compute all
possible future evolutions from a (viable) initial state:

> namespace MonadicTrajectories

>   data StateCtrlSeq : (t : Nat) -> (n : Nat) -> Type where
>     Nil   :  (x : X t) -> StateCtrlSeq t Z
>     (::)  :  (x : X t ** Y t x) -> StateCtrlSeq (S t) n -> StateCtrlSeq t (S n) 

>   postulate stateCtrlTrj  :  (x : X t) -> (r : Reachable x) -> (v : Viable n x) -> 
>                              (ps : PolicySeq t n) -> M (StateCtrlSeq t n)


