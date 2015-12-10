> module Monadic

> import Data.So
> import Data.Fin
> import Control.Isomorphism


Hiding stuff:

> %hide fmap
> %hide Dec

Checking if we use composition (if so it needs to be explained).

> %hide (.)


Require totality:

> %default total

> Prop : Type
> Prop = Type

Syntax extensions:

> namespace RelLib

>   syntax reflexive [alpha] [r] =
>     (a : alpha) -> So (r a a)
>   syntax transitive [alpha] [r] =
>     {a1 : alpha} -> {a2 : alpha} -> {a3 : alpha} ->
>     So (r a1 a2) -> So (r a2 a3) -> So (r a1 a3)
>   syntax monotone [alpha] [r] [op2] =
>     {a1 : alpha} -> {a2 : alpha} ->
>     (a3 : alpha) -> So (r a1 a2) -> So (r (op2 a3 a1) (op2 a3 a2))

> -- end namespace RelLib

Postulates:

> namespace DoubleLib

>   postulate reflexiveDoubleLTE     :  reflexive   Double  (<=)
>   postulate transitiveDoubleLTE    :  transitive  Double  (<=)
>   postulate monotoneDoublePlusLTE  :  monotone    Double  (<=) (+)

> -- end namespace DoubleLib


> namespace NatLib

>   postulate eqInLTE             : (m : Nat) -> (n : Nat) -> m = n -> m `LTE` n
>   postulate idSuccPreservesLTE  : (m : Nat) -> (n : Nat) -> m `LTE` n -> m `LTE` (S n)

> -- end namespace NatLib

Globals:

> namespace SigmaLib

>   outl : {A : Type} -> {P : A -> Prop} -> Sigma A P -> A
>   outl = getWitness
>   outr : {A : Type} -> {P : A -> Prop} -> (s : Sigma A P) -> P (outl s)
>   outr = getProof

> -- end namespace SigmaLib



The theory of monadic sequential decision problems (SDP):


A SDP is specified in terms of a monad ...

> namespace MonadLib

>   M : Type -> Type

>   fmap : {A, B : Type} -> (A -> B) -> M A -> M B
>   -- unused functorSpec1 : fmap . id = id
>   -- unused functorSpec2 : fmap (f . g) = (fmap f) . (fmap g)

>   ret   :  {A : Type} -> A -> M A
>   bind  :  {A, B : Type} -> M A -> (A -> M B) -> M B
>   -- unused monadSpec1   :  (fmap f) . ret = ret . f
>   -- unused monadSpec21  :  bind (ret a) f = f a
>   -- unused monadSpec22  :  bind ma ret = ma
>   -- unused monadSpec23  :  {A, B, C : Type} -> {f : A -> M B} -> {g : B -> M C} ->
>   --                        bind (bind ma f) g = bind ma (\ a => bind (f a) g)

>   join  :  {A : Type} -> M (M A) -> M A
>   join mma = bind mma id

>   certain : {A : Type} -> A -> List A
>   certain a = [a]


> -- end namespace MonadLib

... which is required to be a "container" monad:

> namespace ContainerMonadLib

>   Elem     :  {A : Type} -> A -> M A -> Prop
>   All      :  {A : Type} -> (P : A -> Prop) -> M A -> Prop
>   All {A} P ma = (a : A) -> a `Elem` ma -> P a

>   -- unused containerMonadSpec1  :  a `Elem` (ret a)
>   -- unused containerMonadSpec2  :  {A : Type} -> (a : A) -> (ma : M A) -> (mma : M (M A)) ->
>   --                                a `Elem` ma -> ma `Elem` mma -> a `Elem` (join mma)
>   -- containerMonadSpec3  :  {A : Type} -> {P : A -> Prop} -> {a : A} -> {ma : M A} -> All P ma -> a `Elem` ma -> P a
>   -- containerMonadSpec3 {A} {P} {a} {ma} aPma = aPma a
>   -- unused containerMonadSpec4  :  {A : Type} -> {P : A -> Prop} -> a `Elem` ma -> Not (P a) -> Not (All P ma) -- follows from All

>   tagElem      :  {A : Type} -> (ma : M A) -> M (a : A ** a `Elem` ma)
>   tagElemSpec  :  {A : Type} -> (ma : M A) -> fmap outl (tagElem ma) = ma

> -- end namespace ContainerMonadLib

The standard examples are |M = Id| (deterministic SDP), |M = List|
(non-deterministic SDP) and |M = Prob| (stochastic SDP).

The decision problem itself is specified by giving the decision
process ...

> X : (t : Nat) -> Type

> Y : (t : Nat) -> (x : X t) -> Type

> step    : (t : Nat) -> (x : X t) -> (y : Y t x) -> M (X (S t))

> reward : (t : Nat) -> (x : X t) -> (y : Y t x) -> (x' : X (S t)) -> Double


> rewards : (t : Nat) -> (x : X t) -> (y : Y t x) -> M Double
> rewards t x y = fmap (reward t x y) (step t x y)

... and a measure:

> namespace MeasLib

>   meas : M Double -> Double
>   measMon  :  {A : Type} ->
>               (f : A -> Double) -> (g : A -> Double) ->
>               ((a : A) -> So (f a <= g a)) ->
>               (ma : M A) -> So (meas (fmap f ma) <= meas (fmap g ma))

> -- end namespace MeasLib

For every SDP, we can build the following notions:


  Equivalent problem

> MX : (t : Nat) -> Type
> MX t = M (X t)

> mstep : (t : Nat) -> (mx : MX t) -> (p : ((x : X t) -> Y t x)) -> MX (S t)
> mstep t mx p = join (fmap (\ x => step t x (p x)) mx)

  Simple minded policies:

-- > Policy : (t : Nat) -> Type
-- > Policy t = (x : X t) -> Y t x

-- > data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
-- >   Nil   :  PolicySeq t Z
-- >   (::)  :  Policy t -> PolicySeq (S t) n -> PolicySeq t (S n)


--   Value of (simple minded) policy seqeunces:

-- > val : (x : X t) -> (ps : PolicySeq t n) -> Double
-- > val {t} {n = Z} x ps = 0
-- > val {t} {n = S m} x (p :: ps) = meas (fmap f mx') where
-- >   y : Y t x
-- >   y = p x
-- >   mx' : M (X (S t))
-- >   mx' = step t x y
-- >   f : X (S t) -> Double
-- >   f x' = reward t x y x' + val x' ps

-- > OptPolicySeq : PolicySeq t n -> Prop
-- > OptPolicySeq {t} {n} ps = (ps' : PolicySeq t n) -> (x : X t) -> So (val x ps' <= val x ps)

-- > nilOptPolicySeq : OptPolicySeq Nil
-- > nilOptPolicySeq ps' x = reflexiveDoubleLTE 0


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
> Policy t (S m)  =  (x : X t) -> Reachable x -> Viable (S m) x ->
>                    (y : Y t x ** All (Viable m) (step t x y))

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  PolicySeq t Z
>   (::)  :  Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)


  Value of (refined) policy sequences:

> mutual

>   mkf : (x  : X t) -> (r  : Reachable x) -> (v  : Viable (S m) x) ->
>         (y  : Y t x) -> (av : All (Viable m) (step t x y)) ->
>         (ps : PolicySeq (S t) m) -> (x' : X (S t) ** x' `Elem` (step t x y)) -> Double
>   mkf {t} {m} x r v y av ps (x' ** x'estep) = reward t x y x' + val x' r' v' ps where
>     xpx'  :  x `Pred` x'
>     xpx'  =  Evidence y x'estep
>     r'    :  Reachable x'
>     r'    =  Evidence x (r , xpx')
>     v'    :  Viable m x'
>     v'    =  av x' x'estep

>   val : (x : X t) -> Reachable x -> Viable n x -> PolicySeq t n -> Double
>   val {t} {n = Z} x r v ps = 0
>   val {t} {n = S m} x r v (p :: ps) = meas (fmap f (tagElem mx')) where
>     y    :  Y t x
>     y    =  outl (p x r v)
>     mx'  :  M (X (S t))
>     mx'  =  step t x y
>     av   :  All (Viable m) mx'
>     av   =  outr (p x r v)
>     f    :  (x' : X (S t) ** x' `Elem` mx') -> Double
>     f    =  mkf x r v y av ps


  Optimality of policy sequences:

> OptPolicySeq : PolicySeq t n -> Prop
> OptPolicySeq {t} {n} ps  =  (ps' : PolicySeq t n) -> (x : X t) ->
>                             (r : Reachable x) -> (v : Viable n x) ->
>                             So (val x r v ps' <= val x r v ps)

> nilOptPolicySeq : {t : Nat} -> OptPolicySeq {t = t} {n = Z} Nil
> nilOptPolicySeq {t} ps' x r v = reflexiveDoubleLTE 0


  Optimal extensions of policy sequences:

> OptExt : PolicySeq (S t) m -> Policy t (S m) -> Prop
> OptExt {t} {m} ps p  =  (p' : Policy t (S m)) -> (x : X t) ->
>                         (r : Reachable x) -> (v : Viable (S m) x) ->
>                         So (val x r v (p' :: ps) <= val x r v (p :: ps))


  Bellman's principle of optimality:

> Bellman  :  (ps : PolicySeq (S t) m) -> OptPolicySeq ps ->
>             (p : Policy t (S m)) -> OptExt ps p -> OptPolicySeq (p :: ps)
> Bellman {t} {m} ps ops p oep = opps where
>   opps : OptPolicySeq (p :: ps)
>   opps (p' :: ps') x r v = transitiveDoubleLTE s4 s5 where
>     y'                 :  Y t x
>     y'                 =  outl (p' x r v)
>     mx'                :  M (X (S t))
>     mx'                =  step t x y'
>     av'                :  All (Viable m) mx'
>     av'                =  outr (p' x r v)    
>     f'                 :  (x' : X (S t) ** x' `Elem` mx') -> Double
>     f'                 =  mkf x r v y' av' ps'
>     f                  :  (x' : X (S t) ** x' `Elem` mx') -> Double
>     f                  =  mkf x r v y' av' ps
>     s1                 :  (x' : X (S t)) -> (r' : Reachable x') -> (v' : Viable m x') ->
>                           So (val x' r' v' ps' <= val x' r' v' ps)
>     s1 x' r' v'        =  ops ps' x' r' v'
>     s2                 :  (z : (x' : X (S t) ** x' `Elem` mx')) -> So (f' z <= f z)
>     s2 (x' ** x'emx')  =  monotoneDoublePlusLTE (reward t x y' x') (s1 x' r' v') where
>       xpx'  :  x `Pred` x'
>       xpx'  =  Evidence y' x'emx'
>       r'    :  Reachable x'
>       r'    =  Evidence x (r , xpx')
>       v'    :  Viable m x'
>       v'    =  av' x' x'emx'
>     s3  :  So (meas (fmap f' (tagElem mx')) <= meas (fmap f (tagElem mx')))
>     s3  =  measMon f' f s2 (tagElem mx')
>     s4  :  So (val x r v (p' :: ps') <= val x r v (p' :: ps))
>     s4  =  s3
>     s5  :  So (val x r v (p' :: ps) <= val x r v (p :: ps))
>     s5  =  oep p' x r v

The idea is that, if clients can implement max and argmax

> max         :  {A : Type} -> (f : A -> Double) -> Double
> argmax      :  {A : Type} -> (f : A -> Double) -> A

that fulfill the specification

> maxSpec     :  {A : Type} -> (f : A -> Double) -> (a : A) -> So (f a <= max f)
> argmaxSpec  :  {A : Type} -> (f : A -> Double) -> max f = f (argmax f)

then we can implement a function that computes machine chackable optimal
extensions for arbitrary policy sequences:

> {-
> mkg : (x  : X t) ->
>       (r  : Reachable x) ->
>       (v  : Viable (S n) x) ->
>       (ps : PolicySeq (S t) n) ->
>       (y : Y t x ** All (Viable n) (step t x y)) -> Double
> -- mkg {t} {n} x r v ps (y ** av) = meas (fmap f (tagElem (step t x y))) where
>   -- f : (x' : X (S t) ** x' `Elem` (step t x y)) -> Double
>   -- f = mkf x r v y av ps
> mkg {t} {n} x r v ps yav = meas (fmap f (tagElem (step t x (outl yav)))) where
>   f : (x' : X (S t) ** x' `Elem` (step t x (outl yav))) -> Double
>   f = mkf x r v (outl yav) (outr yav) ps
> -}

> mkg : (x  : X t) -> (r  : Reachable x) ->  (v  : Viable (S n) x) -> 
>       (ps : PolicySeq (S t) n) ->
>       (y : Y t x ** All (Viable n) (step t x y)) -> Double
> mkg {t} {n} x r v ps yav = meas (fmap f (tagElem (step t x (outl yav)))) where
>   f : (x' : X (S t) ** x' `Elem` (step t x (outl yav))) -> Double
>   f = mkf x r v (outl yav) (outr yav) ps

> optExt : PolicySeq (S t) n -> Policy t (S n)
> optExt {t} {n} ps = p where
>   p : Policy t (S n)
>   p x r v = argmax g where
>     g : (y : Y t x ** All (Viable n) (step t x y)) -> Double
>     g = mkg x r v ps
>     -- g (y ** av) = meas (fmap f (tagElem (step t x y))) where
>     --   f : (x' : X (S t) ** x' `Elem` (step t x y)) -> Double
>     --   f = mkf x r v y av ps

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
>   g     :  (y : Y t x ** All (Viable n) (step t x y)) -> Double
>   g     =  mkg x r v ps
>   f     :  (x' : X (S t) ** x' `Elem` (step t x y)) -> Double
>   f     =  mkf x r v y av ps
>   f'    :  (x' : X (S t) ** x' `Elem` (step t x y')) -> Double
>   f'    =  mkf x r v y' av' ps
>   s1    :  So (g yav' <= max g)
>   s1    =  maxSpec g yav'
>   s2    :  So (g yav' <= g (argmax g))
>   s2    =  replace {P = \ z => So (g yav' <= z)} (argmaxSpec g) s1
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
> biLemma t  Z     =  nilOptPolicySeq {t}
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

>   stateCtrlTrj  :  (x : X t) -> (r : Reachable x) -> (v : Viable n x) ->
>                    (ps : PolicySeq t n) -> M (StateCtrlSeq t n)
>   stateCtrlTrj {t} {n = Z}   x r v Nil = ret (Nil x)
>   stateCtrlTrj {t} {n = S m} x r v (p :: ps') = 
>     fmap g (bind (tagElem mx') f) where  
>       y    :  Y t x
>       y    =  outl (p x r v)
>       mx'  :  M (X (S t))
>       mx'  =  step t x y
>       av   :  All (Viable m) mx'
>       av   =  outr (p x r v)
>       g    :  StateCtrlSeq (S t) n -> StateCtrlSeq t (S n) 
>       g    =  ((x ** y) ::)
>       f    :  (x' : X (S t) ** x' `Elem` mx') -> M (StateCtrlSeq (S t) m)
>       f (x' ** x'estep) = stateCtrlTrj {n = m} x' r' v' ps' where
>         xpx'  :  x `Pred` x'
>         xpx'  =  Evidence y x'estep
>         r'    :  Reachable x'
>         r'    =  Evidence x (r , xpx')
>         v'    :  Viable m x'
>         v'    =  av x' x'estep

We can build a theory of avoidability on the top of the theory of
monadic SDPs. First we have to explain what it means for a possible
future state to be avoidable. For this, we have to introduce a
reachability relation:

> ReachableFrom : X t'' -> X t -> Prop
> ReachableFrom  {t'' = Z   }  {t}  x''  x  =  (t = Z ,     x = x'')
> ReachableFrom  {t'' = S t'}  {t}  x''  x  =
>   Either  (t = S t' ,  x = x'') (Exists (\ x' => (x' `ReachableFrom` x , x' `Pred` x'')))

It is easy to show that we are indeed modeling reachability of "future"
states:

> reachableFromLemma : (x'' : X t'') -> (x : X t) -> x'' `ReachableFrom` x -> t'' `GTE` t
> reachableFromLemma {t'' = Z}    {t = Z}    x'' x prf =  
>   LTEZero
> reachableFromLemma {t'' = Z}    {t = S m}  x'' x (prf1 , prf2) = 
>   void (uninhabited u) where
>     u : Z = S m 
>     u = trans (sym prf1) Refl 
> reachableFromLemma {t'' = S t'} {t = Z}    x'' x prf =  
>   LTEZero
> reachableFromLemma {t'' = S t'} {t = S t'} x'' x (Left (Refl , prf2)) =  
>   eqInLTE (S t') (S t') Refl 
> reachableFromLemma {t'' = S t'} {t = t}    x'' x (Right (Evidence x' (prf1 , prf2))) =  
>   s3 where
>     s1  :  t' `GTE` t
>     s1  =  reachableFromLemma x' x prf1
>     s3  :  S t' `GTE` t
>     s3  =  idSuccPreservesLTE t t' s1 

Now we can explain what it means for a state |x'| to be avoidable in a
decision process starting from a previous state |x|:

> Alternative : (x : X t) -> (x' : X t') -> (m : Nat) -> (x'' : X t') -> Prop
> -- Alternative x x' m x'' = (x'' `ReachableFrom` x , Viable m x'' , Not (x'' = x'))
> Alternative x x' m x'' = (x'' `ReachableFrom` x , Viable m x'' , Not (x'' = x'))

> -- AvoidableFrom  :  (x' : X t') -> (x : X t) -> x' `ReachableFrom` x -> Viable n x' -> Prop
> -- AvoidableFrom {t'} {n} x' x r v = Exists (Alternative x x' n)

> AvoidableFrom  :  (x' : X t') -> (x : X t) -> x' `ReachableFrom` x -> (m : Nat) -> Prop
> AvoidableFrom {t'} x' x r m = Exists (Alternative x x' m)

A relevant question for applications is under which conditions
avoidability is decidable. We start by establishing some basic results
about decidability in general:

> namespace DecLibrary

>   data Dec : Prop -> Prop where
>     Yes  : {P : Prop} -> (prf     : P)          -> Dec P
>     No   : {P : Prop} -> (contra  : P -> Void)  -> Dec P

>   Dec0 : Prop -> Prop
>   Dec0 P = Dec P

>   Dec1 : {A : Type} -> (P : A -> Prop) -> Prop
>   Dec1 {A} P  =  (a : A) -> Dec (P a)

>   Dec2 : {A, B : Type} -> (P : A -> B -> Prop) -> Prop
>   Dec2 {A} {B} P  =  (a : A) -> (b : B) -> Dec (P a b)

>   decNot : {P : Prop} -> Dec P -> Dec (Not P)
>   decNot {P} (Yes prf) = No contra where
>     contra : Not P -> Void
>     contra np = np prf
>   decNot {P} (No contra) = Yes contra

>   decEqNat : (m : Nat) -> (n : Nat) -> Dec (m = n)
>   decEqNat Z     Z     = Yes Refl
>   decEqNat Z     (S _) = No ZnotS
>   decEqNat (S _) Z     = No (negEqSym ZnotS)
>   decEqNat (S n) (S m) with (decEqNat n m)
>     | Yes p = Yes $ cong p
>     | No  p = No $ \h : (S n = S m) => p $ succInjective n m h

>   decPair    :  {P, Q : Prop} -> Dec P -> Dec Q -> Dec (P , Q)
>   decPair (Yes p) (Yes q) = Yes (p , q)
>   decPair (Yes p) (No nq) = No (\ pq => nq (snd pq))
>   decPair (No np) (Yes q) = No (\ pq => np (fst pq))
>   decPair (No np) (No nq) = No (\ pq => np (fst pq))

>   decEither  :  {P, Q : Prop} -> Dec P -> Dec Q -> Dec (Either P Q)
>   decEither (Yes p) (Yes q) = Yes (Left p)
>   decEither (Yes p) (No nq) = Yes (Left p)
>   decEither (No np) (Yes q) = Yes (Right q)
>   decEither {P} {Q} (No np) (No nq) = No contra where
>     contra : Either P Q -> Void
>     contra (Left  p) = np p
>     contra (Right q) = nq q

A fundamental result is that, for a finite type |alpha| and a decidable
predicate |P : alpha -> Prop|, |Exists P| is decidable:

>   Finite : Type -> Prop
>   Finite A = Exists (\ n => Iso A (Fin n))

>   postulate finiteDecLemma  :  {A : Type} -> {P : A -> Prop} -> Finite A -> Dec1 P -> Dec (Exists P)

One way of proving |finiteDecLemma| is the one I (Nicola) have presented
at DTP. As you (Cezar, Patrik) have pointed out last time we met at
Chalmers, it might be more efficient (and maybe cleaner and clearer) to
avoid going through a (vector based) representation of the finite type,
prove decidability on the representation and from there deduce the
result. Anyway, I think proving the lemma is an interesting task and
maybe we can have some fun together next time we meet. Maybe the result
is already somewhere in the library, maybe in a slightly different form.

> -- end namespace DecLibrary

To prove decidability of |AvoidableFrom| we obviously need some
additional assumptions. Sufficient conditions are

> decElem : {A : Type} -> (a : A) -> (as : M A) -> Dec (a `Elem` as)
> decAll  :  {A : Type} -> (P : A -> Prop) -> Dec1 P -> (as : M A) -> Dec (All P as)

> decEqX : (x : X t) -> (x' : X t') -> Dec (x = x')
> finX : (t : Nat) -> Finite (X t)
> finY : (t : Nat) -> (x : X t) -> Finite (Y t x)

I guess these are also necessary except maybe from |decAll| which maybe
could be deduced from decidability of membership and from the
specification of monadic containers. Anyway, for decision problems that
fulfill this specification it is easy to prove decidability of
|Viable|

> decViable : (n : Nat) -> (x : X t) -> Dec (Viable n x)
> decViable  Z    x = Yes ()
> decViable {t} (S m) x = finiteDecLemma fY dAll where
>   fY      :  Finite (Y t x)
>   fY      =  finY t x
>   dAll    :  Dec1 (\ y => All (Viable m) (step t x y))
>   dAll y  =  decAll (Viable m) (decViable m) (step t x y)

of |Pred|

> decPred : (x : X t) -> (x' : X (S t)) -> Dec (x `Pred` x')
> decPred {t} x x' = finiteDecLemma fY dElem where
>   fY       :  Finite (Y t x)
>   fY       =  finY t x
>   dElem    :  Dec1 (\ y => x' `Elem` (step t x y))
>   dElem y  =  decElem x' (step t x y)

of |ReachableFrom|

> decReachableFrom : (x'' : X t'') -> (x : X t) -> Dec (x'' `ReachableFrom` x)
> decReachableFrom {t'' = Z   } {t} x'' x = decPair dp dq where
>   dp : Dec (t = Z)
>   dp = decEqNat t Z
>   dq : Dec (x = x'')
>   dq = decEqX x x''
> decReachableFrom {t'' = S t'} {t} x'' x = decEither dp dq where
>   dp : Dec (t = S t' , x = x'')
>   dp = decPair (decEqNat t (S t')) (decEqX x x'')
>   dq : Dec (Exists (\ x' => (x' `ReachableFrom` x , x' `Pred` x'')))
>   dq = finiteDecLemma fX dRP where
>     fX : Finite (X t')
>     fX = finX t'
>     dRP : Dec1 (\ x' => (x' `ReachableFrom` x , x' `Pred` x''))
>     dRP x' = decPair drf dpred where
>       drf : Dec (x' `ReachableFrom` x)
>       drf = decReachableFrom x' x
>       dpred : Dec (x' `Pred` x'')
>       dpred = decPred x' x''

and, finally of |AvoidableFrom|:

> decAlternative : (x : X t) -> (x' : X t') -> (m : Nat) -> (x'' : X t') -> Dec (Alternative x x' m x'')
> decAlternative x x' m x'' = decPair p q where
>   p : Dec (x'' `ReachableFrom` x)
>   p = decReachableFrom x'' x
>   q : Dec (Viable m x'' , Not (x'' = x'))
>   q = decPair (decViable m x'') (decNot (decEqX x'' x'))

> decAvoidableFrom : (x' : X t') ->
>                    (x : X t) ->
>                    x' `ReachableFrom` x ->
>                    (m : Nat) ->
>                    Dec (AvoidableFrom x' x r m)
> decAvoidableFrom {t'} {t} x' x r m = finiteDecLemma fX dA where
>   fX : Finite (X t')
>   fX = finX t'
>   dA : Dec1 (Alternative x x' m)
>   dA x'' = decAlternative x x' m x''


> {-

> ---}
 
