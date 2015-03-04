> module SeqDecProbMonadicExample2


> import Data.Fin
> import Data.Vect
> import Data.So
> import Control.Monad.Identity
> import Control.Isomorphism

> import SeqDecProbMonadic
> import IdentityOperations
> import IdentityProperties
> import BoundedNat
> import BoundedNatOperations
> import BoundedNatProperties
> import SigmaOperations
> import NatProperties
> import Finite
> import FiniteOperations
> import FiniteProperties
> import Unique
> import SoProperties
> import SubType
> import Decidable
> import FiniteSubTypeProperties
> import Prop


> %default total 


We reimplement the example from "S1306_Example2" in the new theory. |M|
is the identity monad:

> SeqDecProbMonadic.M = Identity

> SeqDecProbMonadic.fmap = map

> SeqDecProbMonadic.ret = return

> SeqDecProbMonadic.bind = (>>=)

> SeqDecProbMonadic.Elem = IdentityOperations.Elem

> SeqDecProbMonadic.tagElem = IdentityOperations.tagElem


The decision process:

> maxColumnO2 : Nat
> maxColumnO2 = 2

> maxColumn : Nat
> maxColumn = maxColumnO2 + maxColumnO2

> nColumns : Nat
> nColumns = S maxColumn


States

> SeqDecProbMonadic.X t = LTB nColumns

> column : X t -> Nat
> column = outl

> states : (t : Nat) -> Vect nColumns (X t)
> states t = toVect (\ i => i)


Actions

> data Action = Left | Ahead | Right

> instance Eq Action where
>   (==) Left   Left = True
>   (==) Left      _ = False
>   (==) Ahead Ahead = True
>   (==) Ahead     _ = False
>   (==) Right Right = True
>   (==) Right     _ = False

> instance Show Action where
>   show Left  = "L"
>   show Ahead = "A"
>   show Right = "R"

Action is finite

> to : Action -> Fin 3
> to Left  =        FZ
> to Ahead =     FS FZ
> to Right = FS (FS FZ)

> %assert_total
> from : Fin 3 -> Action
> from         FZ   = Left
> from     (FS FZ)  = Ahead
> from (FS (FS FZ)) = Right

> %assert_total
> toFrom : (k : Fin 3) -> to (from k) = k
> toFrom         FZ   = Refl
> toFrom     (FS FZ)  = Refl
> toFrom (FS (FS FZ)) = Refl

> fromTo : (a : Action) -> from (to a) = a
> fromTo Left  = Refl
> fromTo Ahead = Refl
> fromTo Right = Refl

> fAction : Finite Action
> fAction = Evidence 3 (MkIso to from toFrom fromTo)

> admissible : (t : Nat) -> X t -> Action -> Bool
> admissible t x Ahead = column {t} x == 0 || column {t} x == maxColumn
> admissible t x Left  = column {t} x <= maxColumnO2
> admissible t x Right = column {t} x >= maxColumnO2

> Admissible : (t : Nat) -> X t -> Action -> Type
> Admissible t x a = So (admissible t x a)

> d1Admissible : (t : Nat) -> (x : X t) -> Dec1 (Admissible t x)
> d1Admissible t x = dec1So {A = Action} (admissible t x) 

> u1Admissible : (t : Nat) -> (x : X t) -> Unique1 (Admissible t x)
> u1Admissible t x = unique1So {A = Action} (admissible t x) 


Controls

> SeqDecProbMonadic.Y t x = SubType Action (Admissible t x) (u1Admissible t x)

> action : Y t x -> Action
> action (a ** _) = a


Controls are finite

> fY : (t : Nat) -> (x : X t) -> Finite (Y t x)
> fY t x = finiteSubTypeLemma0 fAction (d1Admissible t x) (u1Admissible t x)


Controls are not empty

> %assert_total
> nefY : (t : Nat) -> (x : X t) -> NonEmpty (fY t x)
> nefY t (Z               ** prf) = nonEmptyLemma (fY t (Z               ** prf)) (Ahead ** Oh)
> nefY t (S Z             ** prf) = nonEmptyLemma (fY t (S Z             ** prf)) (Left  ** Oh)
> nefY t (S (S Z)         ** prf) = nonEmptyLemma (fY t (S (S Z)         ** prf)) (Left  ** Oh)
> nefY t (S (S (S Z))     ** prf) = nonEmptyLemma (fY t (S (S (S Z))     ** prf)) (Right ** Oh)
> nefY t (S (S (S (S Z))) ** prf) = nonEmptyLemma (fY t (S (S (S (S Z))) ** prf)) (Ahead ** Oh)

Transition function

> SeqDecProbMonadic.step t (Z   ** prf) (Left  ** aL) = 
>   Id (maxColumn ** ltIdS maxColumn)
> SeqDecProbMonadic.step t (S n ** prf) (Left  ** aL) = 
>   Id (n ** ltLemma1 n nColumns prf)
> SeqDecProbMonadic.step t (n   ** prf) (Ahead ** aA) = 
>   Id (n ** prf)
> SeqDecProbMonadic.step t (n   ** prf) (Right ** aR) with (decLT n maxColumn) 
>   | (Yes p)     = Id (S n ** LTESucc p)
>   | (No contra) = Id (Z   ** LTESucc LTEZero) 


Reward function

> SeqDecProbMonadic.reward t x y x' = 
>   if column {t = S t} x' == Z
>   then 1.0
>   else if S (column {t = S t} x') == nColumns
>        then 2.0
>        else 0.0


The measure

> SeqDecProbMonadic.meas (Id x) = x

> SeqDecProbMonadic.measMon f g prf (Id x) = prf x


Max and argmax

We want to implement

< max    : (t : Nat) -> (x : X t) -> Viable (S n) x ->
<          (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Float) -> 
<          Float
< argmax : (t : Nat) -> (x : X t) -> Viable (S n) x ->
<          (f : Sigma (Y t x) (\ y => All (Viable n) (step t x y)) -> Float) -> 
<          Sigma (Y t x) (\ y => All (Viable n) (step t x y))

This can be easily done using |Opt.max| and |Opt.argmax|

< max : {A, B : Type} -> {TO : B -> B -> Type} -> 
<       Preordered B TO => 
<       (fA : Finite A) -> (ne : NonEmpty fA) -> 
<       (f : A -> B) -> B
 
if we can show that |Sigma (Y t x) (\ y => All (Viable n) (step t x y))|
is finite and non-empty for every |t : Nat|, |x : X t| such that |Viable
(S n) x|. If we have finiteness

> fYAV : (t : Nat) -> (n : Nat) -> (x : X t) -> Viable (S n) x ->
>        Finite (Sigma (Y t x) (\ y => All (Viable {t = S t} n) (step t x y)))

non-emptiness is straightforward:

> neYAV : (t : Nat) -> (n : Nat) -> (x : X t) -> (v : Viable {t = t} (S n) x) ->
>         NonEmpty (fYAV t n x v)
> neYAV t n x (Evidence y v) = 
>   nonEmptyLemma {A = Sigma (Y t x) (\ y => All (Viable {t = S t} n) (step t x y))} 
>                 (fYAV t n x (Evidence y v)) 
>                 (y ** v)

Thus, the problem is implementing |fYAV|. To this end, it is enough to
show that the predicate |(\ y => All (Viable {t = S t} n) (step t x y))|
is decidable and unique. We start with decidability. First, we derive
decidability of equality on states

> dEqX : {t1, t2 : Nat} -> (x1 : X t1) -> (x2 : X t2) -> Dec (x1 = x2)
> dEqX = decEqLTB

From decidability of equality, decidability of |Elem| and |All| follow:

> dElem : (t : Nat) -> (x : X t) -> (mx : Identity (X t)) -> Dec (SeqDecProbMonadic.Elem x mx)
> dElem t = IdentityProperties.decElem (dEqX {t1 = t} {t2 = t})

> dAll : (t : Nat) -> (P : X t -> Prop) -> Dec1 P -> (mx : Identity (X t)) -> Dec (All P mx) 
> dAll t P dP (Id x) with (dP x)
>   | (Yes prf) = Yes prf' where
>     prf' : (x' : X t) -> x' `IdentityOperations.Elem` (Id x) -> P x'
>     prf' x' x'eqx = replace (sym x'eqx) prf
>   | (No contra) = No contra' where
>     contra' : (f : (x' : X t) -> x' `IdentityOperations.Elem` (Id x) -> P x') -> Void
>     contra' f = contra (f x Refl)

Remark: it would be nice to implement |dAll| by applying a more
general |IdentityProperties.decAll| as done for |dElem|. At this point,
however, it is not clear how a |IdentityProperties.decAll| lemma could
be implemented. The problem is that |All| is defined in
|SeqDecProbMonadic| for every |M : Type -> Type|. Ideally, one would
like to collect the declatations of |Elem|, |tagElem| and the
declaration + definition of |All| in a |MonadicContainer| type class and
then show that |Identity| is an instance of |MonadicContainer|. A first
attempt to realize this design has led to issue #1975 (2015.03.03).

Next, we show that |Viable| is decidable:

> dViable : (t : Nat) -> (n : Nat) -> (x : X t) -> Dec (Viable {t} n x)
> dViable t  Z    x = Yes ()
> dViable t (S m) x = s3 where
>   s1    :  Dec1 (\ y => All (Viable {t = S t} m) (step t x y))
>   s1 y  =  dAll (S t) (Viable {t = S t} m) (dViable (S t) m) (step t x y)
>   s2    :  Dec (Exists {a = Y t x} (\ y => All (Viable {t = S t} m) (step t x y)))
>   s2    =  finiteDecLemma (fY t x) s1
>   s3    :  Dec (Viable {t = t} (S m) x)
>   s3    =  s2

> d1Viable : (t : Nat) -> (n : Nat) -> Dec1 (\ x => Viable {t} n x)
> d1Viable t n x = dViable t n x 

and finally, that the predicate |(\ y => All (Viable {t = S t} n) (step
t x y))| is decidable

> d1AllViable : (t : Nat) -> (n : Nat) -> (x : X t) -> Dec1 (\ y => All (Viable {t = S t} n) (step t x y))
> d1AllViable t n x y = dAll (S t) (Viable {t = S t} n) (d1Viable (S t) n) (step t x y)


Let's turn to uniqueness. We want to show 

> u1AllViable : (t : Nat) -> (n : Nat) -> (x : X t) -> Viable (S n) x ->
>               Unique1 (\ y => All (Viable {t = S t} n) (step t x y))

We proceed as in the case for decidability. We start from uniqueness of
equality on states

> uEqX : {t1, t2 : Nat} -> (x1 : X t1) -> (x2 : X t2) -> Unique (x1 = x2)
> uEqX = uniqueEqLTB

From uniqueness of equality, uniqueness of |Elem| follows:

> uElem : (t : Nat) -> (x : X t) -> (mx : Identity (X t)) -> Unique (SeqDecProbMonadic.Elem x mx)
> uElem t = IdentityProperties.uniqueElem (uEqX {t1 = t} {t2 = t})

Now things get a bit ugly ... I do not think we have a chance of proving

< uAll : (t : Nat) -> (P : X t -> Prop) -> Unique1 P -> (mx : Identity (X t)) -> Unique (All P mx) 

let apart uniqueness of viability proofs. This is because |All P mx| as
defined in |SeqDecProbMonadic|

< All      :  {A : Type} -> (P : A -> Prop) -> M A -> Prop
< All {A} P ma = (a : A) -> a `Elem` ma -> P a

is a function of two arguments and we should prove that any two such
functions are equal. But maybe this is not what we really want to prove
or maybe it is not a good idea to rely on our default implementation of
|All| to fulfill |containerMonadSpec3| per construction. We go on by
postulating |uAll|

> postulate uAll : (t : Nat) -> (P : X t -> Prop) -> Unique1 P -> (mx : Identity (X t)) -> Unique (All P mx) 

and see whether this is useful for getting to |u1AllViable|. But we keep
in mind that, if we had had to implement |All| for |M = Identity|, we
would probably have done something like

> AllIdentity : {A : Type} -> (P : A -> Prop) -> Identity A -> Prop
> AllIdentity {A} P (Id a) = P a

which would triviall fulfill the specification

> containerMonadSpec3Identity : {A : Type} -> {P : A -> Prop} -> 
>                               (a : A) -> 
>                               (ma : M A) -> 
>                               AllIdentity P ma -> 
>                               a `SeqDecProbMonadic.Elem` ma -> 
>                               P a
> containerMonadSpec3Identity {A} {P} a1 (Id a2) pa2 a1eqa2  = replace (sym a1eqa2) pa2

Implementing |uAll| for |All = AllIdentity| should be trivial. This
suggests that we might want to relax the |SeqDecProbMonadic| framework
by reintroducing a specification for |All| instead of a hard-coded
implementation and rely on monad-specific implementations to fulfill
|uAll|. We will see ... for the moment, let's proceed to |uViable|:

> uViable : (t : Nat) -> (n : Nat) -> (x : X t) -> Unique (Viable {t} n x)
> uViable t  Z    x () () = Refl

> uViable t (S m) x p q = s3 where
>   s1    :  Unique1 (\ y => All (Viable {t = S t} m) (step t x y))
>   s1 y  =  uAll (S t) (Viable {t = S t} m) (uViable (S t) m) (step t x y)
>   s2    :  Unique (Exists {a = Y t x} (\ y => All (Viable {t = S t} m) (step t x y)))
>   s2    =  ?kika -- !!!
>   s3    :  p = q
>   s3    =  s2 p q

It is clear that we are not going, in general, to compute |kika|. What
we have to do is to replace the uniqueness requirement with a finiteness
requirement and then apply something like

< finiteSubTypeLemma1 : {A : Type} -> {P : A -> Type} ->
<                       Finite A -> Dec1 P -> (fP : Finite1 P) -> 
<                       Finite (SubType A P fP)

We should probably start with finiteness of products of finite types and
then move to finiteness of dependent pairs.

> -- fYAV : (t : Nat) -> (n : Nat) -> (x : X t) -> Viable (S n) x ->
> --        Finite (Sigma (Y t x) (\ y => All (Viable {t = S t} n) (step t x y)))
> fYAV t n x v = finiteSubTypeLemma0 (fY t x) (d1AllViable t n x) (u1AllViable t n x v)





