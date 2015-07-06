> module SeqDecProbMonadicTheoryRV

> import Data.Fin
> import Data.Vect
> import Control.Isomorphism

> import Prop
> import NatProperties
> import SigmaOperations
> import SigmaProperties
> import Finite
> import FiniteOperations
> import FiniteProperties
> import Decidable
> import DecidableProperties
> import VectOperations
> import VectProperties
> import FinOperations
> import IsomorphismOperations


> %default total


The theory of monadic sequential decision problems (SDP):


A SDP is specified in terms of a monad ...

> M : Type -> Type

> {-
> instance ConatainerMonad M where
> -}

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
> -- All {A} P ma = (a : A) -> a `Elem` ma -> P a
> tagElem  :  {A : Type} -> (ma : M A) -> M (a : A ** a `Elem` ma)

> -- unused containerMonadSpec1 : a `Elem` (ret a)
> -- unused containerMonadSpec2 : {A : Type} -> (a : A) -> (ma : M A) -> (mma : M (M A)) ->
> --                               a `Elem` ma -> ma `Elem` mma -> a `Elem` (join mma)
> containerMonadSpec3 : {A : Type} -> {P : A -> Prop} -> (a : A) -> (ma : M A) ->
>                       All P ma -> a `Elem` ma -> P a
> -- unused tagElemSpec : {A : Type} -> (ma : M A) -> fmap outl (tagElem ma) = ma

The standard examples are |M = Id| (deterministic SDP), |M = List|
(non-deterministic SDP) and |M = Prob| (stochastic SDP).


The decision problem itself is specified by giving the decision
process ...

> X       : (t : Nat) -> Type

> Y       : (t : Nat) -> (x : X t) -> Type

> step    : (t : Nat) -> (x : X t) -> (y : Y t x) -> M (X (S t))

> reward  : (t : Nat) -> (x : X t) -> (y : Y t x) -> (x' : X (S t)) -> Nat

> rewards : (t : Nat) -> (x : X t) -> (y : Y t x) -> M Nat
> rewards t x y = fmap (reward t x y) (step t x y)

... and a measure:

> meas : M Nat -> Nat

> measMon  :  {A : Type} ->
>             (f : A -> Nat) -> (g : A -> Nat) ->
>             ((a : A) -> (f a) `LTE` (g a)) ->
>             (ma : M A) -> (meas (fmap f ma)) `LTE` (meas (fmap g ma))

For every SDP, we can build the following notions:


  Equivalent problem

> MX : (t : Nat) -> Type
> MX t = M (X t)

> mstep : (t : Nat) -> (mx : MX t) -> (p : ((x : X t) -> Y t x)) -> MX (S t)
> mstep t mx p = join (fmap (\ x => step t x (p x)) mx)


  Viability and reachability:

> Viable : (n : Nat) -> X t -> Prop
> -- unused viableSpec0 : (x : X t) -> Viable Z x
> viableSpec1 : (x : X t) -> Viable (S n) x -> Exists {a = Y t x} (\ y => All (Viable n) (step t x y))
> -- unused viableSpec2 : (x : X t) -> Exists (\ y => All (Viable n) (step t x y)) -> Viable (S n) x

> Reachable : X t' -> Prop
> -- unused reachableSpec0 : (x : X Z) -> Reachable x
> reachableSpec1 : (x : X t) -> Reachable {t' = t} x -> (y : Y t x) -> All (Reachable {t' = S t}) (step t x y)
> -- unused reachableSpec2 : (x' : X (S t)) -> Reachable x' -> 
> --                         Exists (\ x => (Reachable x , Exists (\ y => x' `Elem` (step t x y)))) 


  Refined policies:

> Policy : (t : Nat) -> (n : Nat) -> Type
> Policy t Z      =  ()
> -- Policy t (S m)  =  (x : X t) -> Reachable x -> Viable (S m) x -> (y : Y t x ** All (Viable m) (step t x y))
> Policy t (S m)  =  (x : X t) -> Reachable x -> Viable (S m) x -> Subset (Y t x) (\ y => All (Viable m) (step t x y))

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  PolicySeq t Z
>   (::)  :  Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)



  Value of (refined) policy sequences:

> mutual

>   mkf : (x  : X t) -> (r  : Reachable x) -> (v  : Viable (S m) x) ->
>         (y  : Y t x) -> (av : All (Viable m) (step t x y)) ->
>         (ps : PolicySeq (S t) m) ->
>         (x' : X (S t) ** x' `Elem` (step t x y)) -> Nat
>   mkf {t} {m} x r v y av ps (x' ** x'estep) = reward t x y x' + val x' r' v' ps where
>     ar : All Reachable (step t x y)
>     ar = reachableSpec1 x r y
>     r' : Reachable x'
>     r' = containerMonadSpec3 x' (step t x y) ar x'estep
>     v' : Viable m x'
>     v' = containerMonadSpec3 x' (step t x y) av x'estep

>   val : (x : X t) -> Reachable x -> Viable n x -> PolicySeq t n -> Nat
>   val {t} {n = Z} x r v ps = Z
>   val {t} {n = S m} x r v (p :: ps) = meas (fmap f (tagElem mx')) where
>     y    :  Y t x
>     y    =  getWitness (p x r v)
>     mx'  :  M (X (S t))
>     mx'  =  step t x y
>     av   :  All (Viable m) mx'
>     av   =  getProof (p x r v)
>     f    :  (x' : X (S t) ** x' `Elem` mx') -> Nat
>     f    =  mkf x r v y av ps


  Optimality of policy sequences:

> OptPolicySeq : PolicySeq t n -> Prop
> OptPolicySeq {t} {n} ps  =  (ps' : PolicySeq t n) ->
>                             (x : X t) -> (r : Reachable x) -> (v : Viable n x) ->
>                             -- So (val x r v ps' <= val x r v ps)
>                             (val x r v ps') `LTE` (val x r v ps)

> nilOptPolicySeq : OptPolicySeq Nil
> nilOptPolicySeq ps' x r v = reflexiveLTE Z


  Optimal extensions of policy sequences:

> OptExt : PolicySeq (S t) m -> Policy t (S m) -> Prop
> OptExt {t} {m} ps p  =  (p' : Policy t (S m)) ->
>                         (x : X t) -> (r : Reachable x) -> (v : Viable (S m) x) ->
>                         (val x r v (p' :: ps)) `LTE` (val x r v (p :: ps))


  Bellman's principle of optimality:

> Bellman  :  (ps  : PolicySeq (S t) m)  ->   OptPolicySeq ps ->
>             (p   : Policy t (S m))     ->   OptExt ps p ->
>             OptPolicySeq (p :: ps)

> Bellman {t} {m} ps ops p oep = opps where
>   opps : OptPolicySeq (p :: ps)
>   opps (p' :: ps') x r v = transitiveLTE
>                            (val x r v (p' :: ps'))
>                            (val x r v (p' :: ps))
>                            (val x r v (p :: ps))
>                            s4 s5 where
>     y' : Y t x
>     y' = getWitness (p' x r v)
>     mx' : M (X (S t))
>     mx' = step t x y'
>     av' : All (Viable m) mx'
>     av' = getProof (p' x r v)
>     f' : (x' : X (S t) ** x' `Elem` mx') -> Nat
>     f' = mkf x r v y' av' ps'
>     f  : (x' : X (S t) ** x' `Elem` mx') -> Nat
>     f  = mkf x r v y' av' ps
>     s1 : (x' : X (S t)) -> (r' : Reachable x') -> (v' : Viable m x') ->
>          (val x' r' v' ps') `LTE` (val x' r' v' ps)
>     s1 x' r' v' = ops ps' x' r' v'
>     s2 : (z : (x' : X (S t) ** x' `Elem` mx')) -> (f' z) `LTE` (f z)
>     s2 (x' ** x'emx') = monotoneNatPlusLTE (reward t x y' x') (s1 x' r' v') where
>       ar' : All Reachable mx'
>       ar' = reachableSpec1 x r y'
>       r'  : Reachable x'
>       r'  = containerMonadSpec3 x' mx' ar' x'emx'
>       v'  : Viable m x'
>       v'  = containerMonadSpec3 x' mx' av' x'emx'
>     s3 : (meas (fmap f' (tagElem mx'))) `LTE` (meas (fmap f (tagElem mx')))
>     s3 = measMon f' f s2 (tagElem mx')
>     s4 : (val x r v (p' :: ps')) `LTE` (val x r v (p' :: ps))
>     s4 = s3
>     s5 : (val x r v (p' :: ps)) `LTE` (val x r v (p :: ps))
>     s5 = oep p' x r v


The idea is that, if clients can implement max and argmax

> max    : {t : Nat} -> {n : Nat} -> 
>          (x : X t) -> 
>          (Viable (S n) x) ->
>          (f : Subset (Y t x) (\ y => All (Viable n) (step t x y)) -> Nat) ->
>          Nat
> argmax : {t : Nat} -> {n : Nat} -> 
>          (x : X t) -> 
>          (Viable (S n) x) ->
>          (f : Subset (Y t x) (\ y => All (Viable n) (step t x y)) -> Nat) ->
>          Subset (Y t x) (\ y => All (Viable n) (step t x y))

that fulfill the specification

-- > typeHelper : (t : Nat) -> (x : X t) -> Viable (S n) x ->
-- >              (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Nat) ->
-- >              Type
-- > typeHelper t x v f = max x v f = f (argmax x v f)

-- > maxSpec     :  (t : Nat) -> (x : X t) -> (v : Viable {t = t} (S n) x) ->
-- >                -- (f : Sigma (Y t x) (\ y => All (Viable {t = S t} n) (step t x y)) -> Nat) ->
-- >                (f : Subset (Y t x) (\ y => All (Viable {t = S t} n) (step t x y)) -> Nat) ->
-- >                -- (s : Sigma (Y t x) (\ y => All (Viable {t = S t} n) (step t x y))) ->
-- >                (s : Subset (Y t x) (\ y => All (Viable {t = S t} n) (step t x y))) ->
-- >                (f s) `LTE` (max x v f)

-- > argmaxSpec  :  (t : Nat) -> (x : X t) -> (v : Viable (S n) x) ->
-- >                (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Nat) ->
-- >                typeHelper t x v f 
-- >                -- max x v f = f (argmax x v f)

then we can implement a function that computes machine checkable optimal
extensions for arbitrary policy sequences:

> mkg : (x  : X t) ->
>       (r  : Reachable x) ->
>       (v  : Viable (S n) x) ->
>       (ps : PolicySeq (S t) n) ->
>       Subset (Y t x) (\ y => All (Viable n) (step t x y)) -> Nat
> mkg {t} {n} x r v ps (Element y av) = meas (fmap f (tagElem (step t x y))) where
>   f : (x' : X (S t) ** x' `Elem` (step t x y)) -> Nat
>   f = mkf x r v y av ps

> optExt : PolicySeq (S t) n -> Policy t (S n)
> optExt {t} {n} ps = p where
>   p : Policy t (S n)
>   p x r v = argmax x v g where
>     g : Subset (Y t x) (\ y => All (Viable n) (step t x y)) -> Nat
>     g = mkg x r v ps


-- > optExtLemma : (ps : PolicySeq (S t) n) -> OptExt ps (optExt ps)
-- > optExtLemma {t} {n} ps p' x r v = s2 where
-- >   p     :  Policy t (S n)
-- >   p     =  optExt ps
-- >   yav   :  (y : Y t x ** All (Viable n) (step t x y))
-- >   yav   =  p x r v
-- >   y     :  Y t x
-- >   y     =  outl yav
-- >   av    :  All (Viable n) (step t x y)
-- >   av    =  outr yav
-- >   yav'  :  (y : Y t x ** All (Viable n) (step t x y))
-- >   yav'  =  p' x r v
-- >   y'    :  Y t x
-- >   y'    =  outl yav'
-- >   av'   :  All (Viable n) (step t x y')
-- >   av'   =  outr yav'
-- >   g     :  (y : Y t x ** All (Viable n) (step t x y)) -> Nat
-- >   g     =  mkg x r v ps
-- >   f     :  (x' : X (S t) ** x' `Elem` (step t x y)) -> Nat
-- >   f     =  mkf x r v y av ps
-- >   f'    :  (x' : X (S t) ** x' `Elem` (step t x y')) -> Nat
-- >   f'    =  mkf x r v y' av' ps
-- >   s1    :  (g yav') `LTE` (max x v g)
-- >   s1    =  maxSpec t x v g yav'
-- >   s2    :  (g yav') `LTE` (g (argmax x v g))
-- >   s2    =  replace {P = \ z => (g yav' `LTE` z)} (argmaxSpec t x v g) s1
-- >   -- the rest of the steps are for the human reader
-- >   s3    :  (g yav') `LTE` (g yav)
-- >   s3    =  s2
-- >   s4    :  (mkg x r v ps yav') `LTE`  (mkg x r v ps yav)
-- >   s4    =  s3
-- >   s5    :  (meas (fmap f' (tagElem (step t x y')))) `LTE` (meas (fmap f (tagElem (step t x y))))
-- >   s5    =  s4
-- >   s6    :  (val x r v (p' :: ps)) `LTE` (val x r v (p :: ps))
-- >   s6    =  s5


With |optExt|, it is easy to implement a generic machine checkable backwards
induction:

> bi : (t : Nat) -> (n : Nat) -> PolicySeq t n
> bi t  Z     =  Nil
> bi t (S n)  =  let -- ps : PolicySeq (S t) n
>                    ps = bi (S t) n
>                in (optExt ps :: ps)

-- > biLemma : (t : Nat) -> (n : Nat) -> OptPolicySeq (bi t n)
-- > biLemma t  Z     =  nilOptPolicySeq
-- > biLemma t (S n)  =  Bellman ps ops p oep where
-- >   ps   :  PolicySeq (S t) n
-- >   ps   =  bi (S t) n
-- >   ops  :  OptPolicySeq ps
-- >   ops  =  biLemma (S t) n
-- >   p    :  Policy t (S n)
-- >   p    =  optExt ps
-- >   oep  :  OptExt ps p
-- >   oep  =  optExtLemma ps


that is, we can compute provably optimal sequences of policies for
arbitrary SDPs and number of decision steps. The theory can provide
additional support to policy advice, e.g., with methods to compute all
possible future evolutions from a (viable) initial state:

> namespace MonadicTrajectories

>   data StateCtrlSeq : (t : Nat) -> (n : Nat) -> Type where
>     Nil   :  .(x : X t) -> StateCtrlSeq t Z
>     (::)  :  (x : X t ** Y t x) -> StateCtrlSeq (S t) n -> StateCtrlSeq t (S n)

>   stateCtrlTrj  :  (x : X t) -> (r : Reachable x) -> (v : Viable n x) ->
>                    (ps : PolicySeq t n) -> M (StateCtrlSeq t n)

>   stateCtrlTrj {t} {n = Z}   x r v Nil = ret (Nil x)

>   stateCtrlTrj {t} {n = S m} x r v (p :: ps') =
>     fmap g (bind (tagElem mx') f) where
>       y : Y t x
>       y = getWitness (p x r v)
>       mx' : M (X (S t))
>       mx' = step t x y
>       av  : All (Viable m) mx'
>       av  = getProof (p x r v)
>       g : StateCtrlSeq (S t) n -> StateCtrlSeq t (S n)
>       g = ((x ** y) ::)
>       f : (x' : X (S t) ** x' `Elem` mx') -> M (StateCtrlSeq (S t) m)
>       f (x' ** x'estep) = stateCtrlTrj {n = m} x' r' v' ps' where
>         ar : All Reachable (step t x y)
>         ar = reachableSpec1 x r y
>         r' : Reachable x'
>         r' = containerMonadSpec3 x' (step t x y) ar x'estep
>         v' : Viable m x'
>         v' = containerMonadSpec3 x' (step t x y) av x'estep


The major disadvantage of |bi|

< bi : (t : Nat) -> (n : Nat) -> PolicySeq t n
< bi t  Z     =  Nil
< bi t (S n)  =  (optExt ps :: ps) where
<   ps : PolicySeq (S t) n
<   ps = bi (S t) n

is that its computational cost is exponential in the number of
steps. Consider, for example, |bi 0 3|. One has

< bi 0 3
<   = { def. |bi| }
< (optExt (bi 1 2)) :: (bi 1 2)
<   = { def. |bi| }
< (optExt ((optExt (bi 2 1)) :: (bi 2 1))) :: (optExt (bi 2 1)) :: (bi 2 1)
<   = { def. |bi| }
< (optExt ((optExt ((optExt (bi 3 0)) :: (bi 3 0))) :: (optExt (bi 3 0)) :: (bi 3 0))) :: (optExt ((optExt (bi 3 0)) :: (bi 3 0))) :: (optExt (bi 3 0)) :: (bi 3 0)
<   = { def. |bi| }
< (optExt ((optExt ((optExt Nil) :: Nil)) :: (optExt Nil) :: Nil)) :: (optExt ((optExt Nil) :: Nil)) :: (optExt Nil) :: Nil

resulting in

- 4 computations of |optExt Nil|
- 2 computations of |optExt ((optExt Nil) :: Nil)|
- 1 computation of |optExt ((optExt ((optExt Nil) :: Nil)) :: ((optExt Nil) :: Nil))|

or 7 calls to |optExt|. One more decision step implies 15 calls to
|optExt| suggesting that the number of calls to |optExt| for |n|
decision steps is |sum_{i = 0}^{n - 1} 2^j = (1 - 2^n) / (1 - 2)|.

We can make the number of calls to |optExt| linear in |n| by rewriting
|bi| in tail-recursive form. The first step is to replace the recursive
call to |bi| with an iteration. Instead of pattern matching on the
number of steps, we delegate the computation of the policy sequence to
an auxiliary function |ibi| which implements backwards induction
iteratively:

> %assert_total
> ibi : (t : Nat) -> (n : Nat) -> (c : Nat) -> LTE c n ->
>       PolicySeq (n - c + t) c -> PolicySeq t n
> ibi t n c prf ps with (n - c) proof itsEqual
>   |  Z    = replace {P = \ x => PolicySeq (Z + t) x} ceqn
>             ps where
>       ceqn : c = n
>       ceqn = minusLemma3 prf itsEqual
>   | (S m) = ibi t n (S c) prf' ps' where
>       prf' : LTE (S c) n
>       prf' = minusLemma2 prf (sym itsEqual)
>       ps'  : PolicySeq (n - (S c) + t) (S c)
>       ps'  = replace {P = \ x => PolicySeq (x + t) (S c)} (minusLemma1 (sym itsEqual))
>              ((optExt ps) :: ps)

> trbi : (t : Nat) -> (n : Nat) -> PolicySeq t n
> trbi t n = ibi t n Z LTEZero Nil

We can easily check that |trbi 0 3| and |bi 0 3| reduce to the same expression

< trbi 0 3
<   = {def. |trbi|}
< ibi 0 3 0 LTEZero
< Nil
<   = {def. |ibi|}
< ibi 0 3 1 (...)
< (optExt Nil) :: Nil
<   = {def. |ibi|}
< ibi 0 3 2 (...)
< (optExt ((optExt Nil) :: Nil)) :: (optExt Nil) :: Nil
<   = {def. |ibi|}
< ibi 0 3 3 (...)
< (optExt ((optExt ((optExt Nil) :: Nil)) :: (optExt Nil) :: Nil)) :: (optExt ((optExt Nil) :: Nil)) :: (optExt Nil) :: Nil
<   = {def. |ibi|}
< (optExt ((optExt ((optExt Nil) :: Nil)) :: (optExt Nil) :: Nil)) :: (optExt ((optExt Nil) :: Nil)) :: (optExt Nil) :: Nil

...

The second step ...


> namespace TabulatedBackwardsInduction

If the state space is finite

>   fX : (t : Nat) -> Finite (X t)     -- Assumption

one can compute the number of values of type |X t| and collect them in a
vector

>   cX : (t : Nat) -> Nat
>   cX t = card (fX t)

>   rX : (t : Nat) -> Vect (cX t) (X t)
>   rX t = toVect (fX t)

If |Reachable| and |Viable n| are also decidable

>   dReachable : {t' : Nat} -> (x' : X t') -> Dec (Reachable x')
>   dViable : {t : Nat} -> (n : Nat) -> (x : X t) -> Dec (Viable n x)

then their conjunction

>   ReachableViable : {t : Nat} -> (n : Nat) -> (x : X t) -> Prop
>   ReachableViable n x = (Reachable x , Viable n x)

is also decidable

>   dReachableViable : {t : Nat} -> (n : Nat) -> (x : X t) -> Dec (ReachableViable n x)
>   dReachableViable n x = decPair (dReachable x) (dViable n x)

and one can collect all states which are reachable and viable in a vector:

TODO: Check if we can use Subset to erase the ReachableViable component during compilation.

>   crRVX : (t : Nat) -> (n : Nat) -> Sigma Nat (\ m => Vect m (Subset (X t) (ReachableViable n)))
>   crRVX t n = filterTagSubset (dReachableViable n) (rX t)

>   cRVX : (t : Nat) -> (n : Nat) -> Nat
>   cRVX t n = getWitness (crRVX t n)

>   rRVX : (t : Nat) -> (n : Nat) -> Vect (cRVX t n) (Subset (X t) (ReachableViable n))
>   rRVX t n = getProof (crRVX t n)

In this case one can implement a "tabulated" versions of |bi| which is
linear in the number of steps. The starting point is an implementation
of |optExt| based on an accumulator. Remember that |optExt| takes a
policy sequence for |n| steps and computes a policy sequence for |n + 1|
steps:

< optExt : PolicySeq (S t) n -> Policy t (S n)

The idea is to equip |optExt| with an additional argument |vt : Vect
(cRVX t n) Nat|, the so-called "value table"

  tabOptExt : (ps : PolicySeq (S t) n) -> (vt : Vect (cRVX (S t) n) Nat) -> Policy t (S n)

>   tabOptExt : (vt : Vect (cRVX (S t) n) Nat) -> Policy t (S n)

storing the value, for a given |ps : PolicySeq (S t) n| and for every
state in |RVX t (S n)|, of taking |n| decision steps with |ps| starting
from that state:

> {-
>   vtLemma : (t : Nat) -> (n : Nat) ->
>             (ps : PolicySeq (S t) n) -> (vt : Vect (cRVX (S t) n) Nat) ->
>             (x : X (S t)) -> (r : Reachable x) -> (v : Viable n x) ->
>             index (lookup (x ** (r , v)) (rRVX (S t) n) (rRVXcomplete (S t) n (x ** (r , v)))) vt
>             =
>             val x r v ps
> -}

Under these assumption, one can implement |tabOptExt| from |optExt| by
just replacing |ps : PolicySeq (S t) n| with |vt : Vect (cRVX (S t) n)
Nat|:

>   mkf' : {t : Nat} -> {n : Nat} ->
>          (x  : X t) -> 
>          .(r  : Reachable x) -> 
>          .(v  : Viable (S n) x) ->
>          (y  : Y t x) -> 
>          (av : All (Viable n) (step t x y)) ->
>          (vt : Vect (cRVX (S t) n) Nat) ->
>          (x' : X (S t) ** x' `Elem` (step t x y)) -> Nat
>   mkf' {t} {n} x r v y av vt (x' ** x'estep) = reward t x y x' + index k vt where
>     rvxs : Vect (cRVX (S t) n) (X (S t))
>     rvxs = map getWitness (rRVX (S t) n)
>     ar : All Reachable (step t x y)
>     ar = reachableSpec1 x r y
>     r' : Reachable x'
>     r' = containerMonadSpec3 x' (step t x y) ar x'estep
>     v' : Viable n x'
>     v' = containerMonadSpec3 x' (step t x y) av x'estep
>     k    : Fin (cRVX (S t) n)
>     k    = lookup x' rvxs prf' where
>       dRV : Dec1 (ReachableViable n)
>       dRV = dReachableViable n
>       prf : Elem x' (rX (S t))
>       prf = toVectComplete (fX (S t)) x'
>       prf' : Elem x' rvxs
>       prf' = filterTagSubsetLemma {P = ReachableViable n} dRV x' (rX (S t)) prf (r',v')

>   mkg : {t : Nat} -> {n : Nat} ->
>         (x  : X t) ->
>         .(r  : Reachable x) ->
>         .(v  : Viable (S n) x) ->
>         (vt : Vect (cRVX (S t) n) Nat) -> 
>         Subset (Y t x) (\ y => All (Viable n) (step t x y)) -> Nat
>   mkg {t} x r v vt (Element y av) = meas (fmap f' (tagElem (step t x y))) where
>     f' : (x' : X (S t) ** x' `Elem` (step t x y)) -> Nat
>     f' = mkf' x r v y av vt

>   tabOptExt {t} {n} vt = p where
>     p : Policy t (S n)
>     p x r v = argmax x v g where
>       g : Subset (Y t x) (\ y => All (Viable n) (step t x y)) -> Nat
>       g = mkg x r v vt

With |tabOptExt| in place, it is easy to implement a tabulated version
of |trbi|:

> ValueTable : Nat -> Nat -> Type
> ValueTable t n = Vect (cRVX t n) Nat  -- a table of the result of calling flip val (roughly) on a PolicySeq

> PolicySeqAndTab : Nat -> Nat -> Type
> PolicySeqAndTab t n = (PolicySeq t n, ValueTable t n)

> zeroVec : (n : Nat) -> Vect n Nat
> zeroVec Z     = Nil
> zeroVec (S n) = Z :: zeroVec n


> ||| Tabulated backwards induction
> biT : (t : Nat) -> (n : Nat) -> PolicySeqAndTab t n
> biT t  Z     =  (Nil, zeroVec _)
> biT t (S n)  =  (p :: ps , vt') where
>      psvt : PolicySeqAndTab (S t) n
>      psvt = biT (S t) n
>      ps : PolicySeq (S t) n
>      ps = fst psvt
>      vt : ValueTable (S t) n
>      vt = snd psvt
>      p : Policy t (S n)
>      p = tabOptExt vt
>      vt' : ValueTable t (S n)
>      vt' = toVect vtf where
>         vtf : Fin (cRVX t (S n)) -> Nat
>         vtf k = g yav where
>           xrv : Subset (X t) (ReachableViable (S n))
>           xrv = index k (rRVX t (S n))
>           x   : X t
>           x   = getWitness xrv
>           rv  : ReachableViable (S n) x
>           rv  = getProof xrv
>           r   : Reachable x
>           r   = fst rv
>           v   : Viable (S n) x
>           v   = snd rv
>           g   : Subset (Y t x) (\ y => All (Viable n) (step t x y)) -> Nat
>           g   = mkg x r v vt
>           yav : Subset (Y t x) (\ y=> All (Viable n) (step t x y))
>           yav = p x r v


> ||| Tabulated tail-recursive backwards induction
> tabibi : (t : Nat) -> (n : Nat) -> (c : Nat) -> .(LTE c n) ->
>          PolicySeq (c + t) (n - c) ->
>          (vt : Vect (cRVX (c + t) (n - c)) Nat) ->
>          PolicySeq t n
>
> tabibi t n  Z     prf ps vt = replace {P = \ z => PolicySeq t z} (minusZeroRight n) ps
>
> tabibi t n (S c') prf ps vt = tabibi t n c' prf' ps' vt'' where
>   bic  : S (n - S c') = n - c'
>   bic  = minusLemma4 prf
>   prf' : LTE c' n
>   prf' = believe_me True -- lteLemma1 c' n prf
>   p    : Policy (c' + t) (S (n - S c'))
>   p    = tabOptExt vt
>   ps'  : PolicySeq (c' + t) (n - c')
>   ps'  = replace {P = \ z => PolicySeq (c' + t) z} bic (p :: ps)
>   vt'  : Vect (cRVX (c' + t) (S (n - S c'))) Nat
>   vt'  = toVect vt'f where
>     vt'f : Fin (cRVX (c' + t) (S (n - S c'))) -> Nat
>     vt'f k = g yav where
>       xrv : Subset (X (c' + t)) (ReachableViable (S (n - S c')))
>       xrv = index k (rRVX (c' + t) (S (n - S c')))
>       x   : X (c' + t)
>       x   = getWitness xrv
>       r   : Reachable {t' = c' + t} x
>       r   = fst (getProof xrv)
>       v   : Viable {t = c' + t} (S (n - S c')) x
>       v   = snd (getProof xrv)
>       g   : Subset (Y (c' + t) x) (\ y => All (Viable (n - (S c'))) (step (c' + t) x y)) -> Nat
>       g   = mkg x r v vt
>       yav : Subset (Y (c' + t) x) (\ y => All (Viable (n - (S c'))) (step (c' + t) x y))
>       yav = p x r v
>   vt''  : Vect (cRVX (c' + t) (n - c')) Nat
>   vt''  = replace {P = \z => Vect (cRVX (c' + t) z) Nat} bic vt'


> |||
> tabtrbi : (t : Nat) -> (n : Nat) -> PolicySeq t n
> tabtrbi t n = tabibi t n n (reflexiveLTE n) zps (zeroVec _) where
>   zps : PolicySeq (n + t) (n - n)
>   zps = replace {P = \ z => PolicySeq (n + t) z} (minusZeroN n) Nil

> ---}
