> module SeqDecProbsTabulatedBackwardsInduction

> import Data.Fin
> import Data.Vect

> import SeqDecProbsCoreAssumptions
> import SeqDecProbsCoreTheory

> import NatOperations
> import NatProperties
> import Sigma
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


> %default total
> %access public export


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

... If the state space is finite

> fState : (t : Nat) -> Finite (State t) -- Assumption

one can compute the number of values of type |State t| and collect them in a
vector

> cState : (t : Nat) -> Nat
> cState t = card (fState t)

> rState : (t : Nat) -> Vect (cState t) (State t)
> rState t = toVect (fState t)

If |Reachable| and |Viable n| are also decidable

> dReachable : {t' : Nat} -> (x' : State t') -> Dec (Reachable x')
> dViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Dec (Viable n x)

then their conjunction

> ReachableViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Type
> ReachableViable n x = (Reachable x , Viable n x)

is also decidable

> dReachableViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Dec (ReachableViable n x)
> dReachableViable n x = decPair (dReachable x) (dViable n x)

and one can collect all states which are reachable and viable in a vector:

> crRVState : (t : Nat) -> (n : Nat) -> Sigma Nat (\ m => Vect m (Sigma (State t) (ReachableViable n)))
> crRVState t n = filterTagSigma (dReachableViable n) (rState t)

> cRVState : (t : Nat) -> (n : Nat) -> Nat
> cRVState t n = outl (crRVState t n)

> rRVState : (t : Nat) -> (n : Nat) -> Vect (cRVState t n) (Sigma (State t) (ReachableViable n))
> rRVState t n = outr (crRVState t n)

In this case one can implement a "tabulated" versions of |bi| which is
linear in the number of steps. The starting point is an implementation
of |optExt| based on an accumulator. Remember that |optExt| takes a
policy sequence for |n| steps and computes a policy sequence for |n + 1|
steps:

< optExt : PolicySeq (S t) n -> Policy t (S n)

The idea is to equip |optExt| with an additional argument |vt : Vect
(cRVState t n) Nat|, the so-called "value table"

< tabOptExt : (ps : PolicySeq (S t) n) -> (vt : Vect (cRVState (S t) n) Nat) -> Policy t (S n)

> tabOptExt : (vt : Vect (cRVState (S t) n) Nat) -> Policy t (S n)

storing the value, for a given |ps : PolicySeq (S t) n| and for every
state in |RVState t (S n)|, of taking |n| decision steps with |ps| starting
from that state:

> {-
>   vtLemma : (t : Nat) -> (n : Nat) ->
>             (ps : PolicySeq (S t) n) -> (vt : Vect (cRVState (S t) n) Nat) ->
>             (x : State (S t)) -> (r : Reachable x) -> (v : Viable n x) ->
>             index (lookup (x ** (r , v)) (rRVState (S t) n) (rRVStatecomplete (S t) n (x ** (r , v)))) vt
>             =
>             val x r v ps
> -}

Under these assumption, one can implement |tabOptExt| from |optExt| by
just replacing |ps : PolicySeq (S t) n| with |vt : Vect (cRVState (S t) n)
Nat|:

> mkf' : {t : Nat} -> {n : Nat} ->
>        (x  : State t) -> 
>        (r  : Reachable x) -> 
>        (v  : Viable (S n) x) ->
>        (y  : Ctrl t x) -> 
>        (av : All (Viable n) (step t x y)) ->
>        (vt : Vect (cRVState (S t) n) Nat) ->
>        Sigma (State (S t)) (\ x' => x' `Elem` (step t x y)) -> Nat
> mkf' {t} {n} x r v y av vt (MkSigma x' x'estep) = reward t x y x' + index k vt where
>   rvxs : Vect (cRVState (S t) n) (State (S t))
>   rvxs = map outl (rRVState (S t) n)
>   ar : All Reachable (step t x y)
>   ar = reachableSpec1 x r y
>   r' : Reachable x'
>   r' = containerMonadSpec3 x' (step t x y) ar x'estep
>   v' : Viable n x'
>   v' = containerMonadSpec3 x' (step t x y) av x'estep
>   k    : Fin (cRVState (S t) n)
>   k    = lookup x' rvxs prf' where
>     dRV : Dec1 (ReachableViable n)
>     dRV = dReachableViable n
>     prf : Elem x' (rState (S t))
>     prf = toVectComplete (fState (S t)) x'
>     prf' : Elem x' rvxs
>     prf' = filterTagSigmaLemma {P = ReachableViable n} dRV x' (rState (S t)) prf (r',v')

> mkg : {t : Nat} -> {n : Nat} ->
>       (x  : State t) ->
>       (r  : Reachable x) ->
>       (v  : Viable (S n) x) ->
>       (vt : Vect (cRVState (S t) n) Nat) -> 
>       Sigma (Ctrl t x) (\ y => All (Viable n) (step t x y)) -> Nat
> mkg {t} x r v vt (MkSigma y av) = meas (fmap f' (tagElem (step t x y))) where
>   f' : Sigma (State (S t)) (\ x' => x' `Elem` (step t x y)) -> Nat
>   f' = mkf' x r v y av vt

> tabOptExt {t} {n} vt = p where
>   p : Policy t (S n)
>   p x r v = argmax x v g where
>     g : Sigma (Ctrl t x) (\ y => All (Viable n) (step t x y)) -> Nat
>     g = mkg x r v vt

With |tabOptExt| in place, it is easy to implement a tabulated version
of |trbi|:

> ValueTable : Nat -> Nat -> Type
> ValueTable t n = Vect (cRVState t n) Nat  -- a table of the result of calling flip val (roughly) on a PolicySeq

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
>         vtf : Fin (cRVState t (S n)) -> Nat
>         vtf k = g yav where
>           xrv : Sigma (State t) (ReachableViable (S n))
>           xrv = index k (rRVState t (S n))
>           x   : State t
>           x   = outl xrv
>           rv  : ReachableViable (S n) x
>           rv  = outr xrv
>           r   : Reachable x
>           r   = fst rv
>           v   : Viable (S n) x
>           v   = snd rv
>           g   : Sigma (Ctrl t x) (\ y => All (Viable n) (step t x y)) -> Nat
>           g   = mkg x r v vt
>           yav : Sigma (Ctrl t x) (\ y => All (Viable n) (step t x y))
>           yav = p x r v


> ||| Tabulated tail-recursive backwards induction
> tabibi : (t : Nat) -> (n : Nat) -> (c : Nat) -> (LTE c n) ->
>          PolicySeq (c + t) (n - c) ->
>          (vt : Vect (cRVState (c + t) (n - c)) Nat) ->
>          PolicySeq t n
>
> tabibi t n  Z     prf ps vt = replace {P = \ z => PolicySeq t z} (minusZeroRight n) ps
>
> tabibi t n (S c') prf ps vt = tabibi t n c' prf' ps' vt'' where
>   bic  : S (n - S c') = n - c'
>   bic  = minusLemma4 prf
>   prf' : LTE c' n
>   prf' = lteLemma1 c' n prf
>   p    : Policy (c' + t) (S (n - S c'))
>   p    = tabOptExt vt
>   ps'  : PolicySeq (c' + t) (n - c')
>   ps'  = replace {P = \ z => PolicySeq (c' + t) z} bic (p :: ps)
>   vt'  : Vect (cRVState (c' + t) (S (n - S c'))) Nat
>   vt'  = toVect vt'f where
>     vt'f : Fin (cRVState (c' + t) (S (n - S c'))) -> Nat
>     vt'f k = g yav where
>       xrv : Sigma (State (c' + t)) (ReachableViable (S (n - S c')))
>       xrv = index k (rRVState (c' + t) (S (n - S c')))
>       x   : State (c' + t)
>       x   = outl xrv
>       r   : Reachable {t' = c' + t} x
>       r   = fst (outr xrv)
>       v   : Viable {t = c' + t} (S (n - S c')) x
>       v   = snd (outr xrv)
>       g   : Sigma (Ctrl (c' + t) x) (\ y => All (Viable (n - (S c'))) (step (c' + t) x y)) -> Nat
>       g   = mkg x r v vt
>       yav : Sigma (Ctrl (c' + t) x) (\ y => All (Viable (n - (S c'))) (step (c' + t) x y))
>       yav = p x r v
>   vt''  : Vect (cRVState (c' + t) (n - c')) Nat
>   vt''  = replace {P = \z => Vect (cRVState (c' + t) z) Nat} bic vt'


> |||
> tabtrbi : (t : Nat) -> (n : Nat) -> PolicySeq t n
> tabtrbi t n = tabibi t n n (reflexiveLTE n) zps (zeroVec _) where
>   zps : PolicySeq (n + t) (n - n)
>   zps = replace {P = \ z => PolicySeq (n + t) z} (minusZeroN n) Nil


> {-

> ---}
