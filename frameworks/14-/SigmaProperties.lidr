> module SigmaProperties

> import Data.Fin
> import Data.Vect
> import Control.Isomorphism

> import Decidable
> import Finite
> import Unique
> import Sigma
> import PairsOperations
> import SigmaOperations
> import VectOperations
> import VectProperties
> import FiniteOperations
> import FiniteProperties
> import FinOperations
> import IsomorphismOperations
> import IsomorphismProperties
> import Basics

> %default total
> %access public export


Equality of projections:

> ||| Equality of first projections
> getWitnessPreservesEq : {A  : Type} ->
>                         {P  : A -> Type} ->
>                         {s1 : Sigma A P} ->
>                         {s2 : Sigma A P} ->
>                         .(s1 = s2) -> (getWitness s1 = getWitness s2)
> getWitnessPreservesEq {s1 = MkSigma a p} {s2 = MkSigma a p} Refl = Refl
> %freeze getWitnessPreservesEq


> ||| Equality of second projections
> getProofPreservesEq : {A  : Type} ->
>                       {P  : A -> Type} ->
>                       {s1 : Sigma A P} ->
>                       {s2 : Sigma A P} ->
>                       .(s1 = s2) -> (getProof s1 = getProof s2)
> getProofPreservesEq {s1 = MkSigma a p} {s2 = MkSigma a p} Refl = Refl
> %freeze getProofPreservesEq


Equality of Sigma types:

> ||| Introduction
> sigmaEqLemma2 : {A : Type} ->
>                 {P : A -> Type} ->
>                 {s1: Sigma A P} ->
>                 {s2: Sigma A P} ->
>                 .(getWitness s1 = getWitness s2) ->
>                 .(getProof s1 = getProof s2) ->
>                 s1 = s2
> sigmaEqLemma2 {A} {P} {s1 = MkSigma a p} {s2 = MkSigma a p} Refl Refl = Refl
> %freeze sigmaEqLemma2


> ||| Elimination and formation
> sigmaEqLemma0 : {A : Type} ->
>                 {P : A -> Type} ->
>                 .(s: Sigma A P) ->
>                 s = MkSigma (getWitness s) (getProof s)
> sigmaEqLemma0 (MkSigma a p) = Refl
> %freeze sigmaEqLemma0


> ||| Equality for singleton predicates
> sigmaEqLemma1 : {A  : Type} ->
>                 {P  : A -> Type} ->
>                 (s1 : Sigma A P) ->
>                 (s2 : Sigma A P) ->
>                 getWitness s1 = getWitness s2 ->
>                 Unique0 (P (getWitness s1)) ->
>                 s1 = s2
> -- sigmaEqLemma1 (a ** p) (a ** q) Refl uP = cong (uP p q)
> sigmaEqLemma1 (MkSigma a p) (MkSigma a' q) prf uP with (prf)
>   sigmaEqLemma1 (MkSigma a p) (MkSigma a q) prf uP | (Refl) = cong (uP p q)
> %freeze sigmaEqLemma1


Decidability of Sigma equality:

> ||| Decidability of equality 1
> sigmaDecEqLemma1 : {A : Type} ->
>                    {P : A -> Type} ->
>                    (DecEq0 A) ->
>                    (DecEq1 P) ->
>                    (s1 : Sigma A P) ->
>                    (s2 : Sigma A P) ->
>                    Dec (s1 = s2)
> sigmaDecEqLemma1 da d1p (MkSigma a1 pa1) (MkSigma a2 pa2)     with (da a1 a2)
>   sigmaDecEqLemma1 da d1p (MkSigma a1 pa1) (MkSigma a1 pa2)   | (Yes Refl) with ((d1p a1) pa1 pa2)
>     sigmaDecEqLemma1 da d1p (MkSigma a1 pa1) (MkSigma a1 pa1) | (Yes Refl) | (Yes Refl) = Yes Refl
>     sigmaDecEqLemma1 da d1p (MkSigma a1 pa1) (MkSigma a1 pa2) | (Yes Refl) | (No contra) = No (\ eq => contra (getProofPreservesEq eq))
>   sigmaDecEqLemma1 da d1p (MkSigma a1 pa1) (MkSigma a2 pa2)   | (No contra) = No (\ eq => contra (getWitnessPreservesEq eq))
> %freeze sigmaDecEqLemma1


> ||| Decidability of equality 2
> sigmaDecEqLemma2 : {A : Type} ->
>                    {P : A -> Type} ->
>                    (DecEq A) ->
>                    (Unique1 P) ->
>                    (s1 : Sigma A P) ->
>                    (s2 : Sigma A P) ->
>                    Dec (s1 = s2)
> sigmaDecEqLemma2 da p1P s1 s2 with (decEq (getWitness s1) (getWitness s2))
>   | (Yes prf)   = Yes (sigmaEqLemma1 s1 s2 prf (p1P (getWitness s1)))
>   | (No contra) = No (\ eq => contra (getWitnessPreservesEq eq))
> %freeze sigmaDecEqLemma2

We want to show that |toVect| is complete

< toVectSigmaComplete : {A   : Type} ->
<                       {P   : A -> Type} ->
<                       .(fA  : Finite A) ->
<                       .(d1P : Dec1 P) ->
<                       .(Unique1 {t0 = A} P) ->
<                       .(s   : Sigma A P) ->
<                       Elem s (getProof (toVectSigma fA d1P))

We start by deriving two auxiliary results. The first one is

> |||
> toVectSigmaLemma : {A : Type} ->
>                    {P : A -> Type} ->
>                    (fA : Finite A) ->
>                    (d1P : Dec1 P) ->
>                    (a : A) ->
>                    (p : P a) ->
>                    Elem a (map Sigma.getWitness (getProof (toVectSigma fA d1P)))
> toVectSigmaLemma {A} {P} fA d1P a p =
>   filterTagSigmaLemma d1P a (toVect fA) (toVectComplete fA a) p
> %freeze toVectSigmaLemma

The proof is computed by applying |VectProperties.filterTagSigmaLemma|:

< filterTagSigmaLemma : {A : Type} -> {P : A -> Type} ->
<                       (d1P : Dec1 P) ->
<                       (a : A) ->
<                       (as : Vect n A) ->
<                       (Elem a as) ->
<                       (p : P a) ->
<                       Elem a (map getWitness (getProof (filterTagSigma d1P as)))

to |d1P|, |a|, to the vector-based representation of |A| associated to
|fA| provided by |FiniteOperations.toVect fA| and to a proof that |a| is
an element of |FiniteOperations.toVect fA|. The latter follows from
completeness of |toVect|, see |FiniteProperties.toVectComplete|. In this
form, |toVectLemma| does not type check.

The second result is

> |||
> sigmaUniqueLemma1 : {A   : Type} ->
>                     {P   : A -> Type} ->
>                     (Unique1 P) ->
>                     (a : A) ->
>                     (p : P a) ->
>                     (ss : Vect n (Sigma A P)) ->
>                     (Elem a (map Sigma.getWitness ss)) ->
>                     Elem (MkSigma a p) ss
> sigmaUniqueLemma1 u1P a p Nil prf = absurd prf
> sigmaUniqueLemma1 u1P a p ((MkSigma a q) :: ss) (Here {x = a}) with (u1P a p q)
>   sigmaUniqueLemma1 u1P a p ((MkSigma a p) :: ss) (Here {x = a}) | Refl =
>     Here {x = (MkSigma a p)} {xs = ss}
> sigmaUniqueLemma1 u1P a1 p1 ((MkSigma a2 p2) :: ss) (There prf) =
>   There (sigmaUniqueLemma1 u1P a1 p1 ss prf)
> %freeze sigmaUniqueLemma1

With |toVectLemma| and |sigmaUniqueLemma1|, it is easy to show that
|toVect| is complete:

> |||
> toVectSigmaComplete : {A   : Type} ->
>                       {P   : A -> Type} ->
>                       (fA  : Finite A) ->
>                       (d1P : Dec1 P) ->
>                       (u1P : Unique1 P) ->
>                       (s   : Sigma A P) ->
>                       Elem s (getProof (toVectSigma fA d1P))
> toVectSigmaComplete fA d1P u1P (MkSigma a p) = s1 where
>   s0 : Elem a (map Sigma.getWitness (getProof (toVectSigma fA d1P)))
>   s0 = toVectSigmaLemma fA d1P a p
>   s1 : Elem (MkSigma a p) (getProof (toVectSigma fA d1P))
>   s1 = sigmaUniqueLemma1 u1P a p (getProof (toVectSigma fA d1P)) s0
> %freeze toVectSigmaComplete

> {-
> toVectSigmaInjective1 : {A   : Type} ->
>                         {P   : A -> Type} ->
>                        .(fA  : Finite A) ->
>                        .(d1P : Dec1 P) ->
>                        .(Unique1 {t0 = A} P) ->
>                        Injective1 (getProof (toVectSigma fA d1P))
> toVectSigmaInjective1 fA dP uP =
>   injectiveFilterTagSigmaLemma dP (toVect fA) (toVectInjective1 fA)
> -}


Sigma Fin properties:

> using (P : Fin Z -> Type)
>   implementation Uninhabited (Sigma (Fin Z) P) where
>     uninhabited (MkSigma k _) = absurd k


> |||
> isoReplaceLemma1 : {A, A' : Type} ->  {B : A -> Type} -> {B' : A' -> Type} ->
>                    (isoA : Iso A A') ->
>                    (isoBa  : (a : A) -> Iso (B a) (B' (to isoA a)) ) ->
>                    (a' : A') -> (b' : B' a') ->
>                    to (isoBa (from isoA a')) (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b'))
>                    =
>                    b'
> isoReplaceLemma1 isoA isoBa a' b' = trans s1 s2 where
>   s1 : to (isoBa (from isoA a')) (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b'))
>        =
>        (replace (sym (toFrom isoA a')) b')
>   s1 = toFrom (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b')
>   s2 : replace (sym (toFrom isoA a')) b' = b'
>   s2 = replaceLemma (sym (toFrom isoA a')) b'
> %freeze isoReplaceLemma1


> |||
> isoReplaceLemma2 : {A, A' : Type} ->  {B : A -> Type} -> {B' : A' -> Type} ->
>                    (isoA : Iso A A') ->
>                    (isoBa  : (a : A) -> Iso (B a) (B' (to isoA a)) ) ->
>                    (a : A) -> (b : B a) ->
>                    from (isoBa (from isoA (to isoA a))) (replace (sym (toFrom isoA (to isoA a))) (to (isoBa a) b))
>                    =
>                    b
> isoReplaceLemma2 {A} {A'} {B} {B'} isoA isoBa a b = trans s2 s3 where
>   s1 : replace (sym (toFrom isoA (to isoA a))) (to (isoBa a) b)
>        =
>        to (isoBa a) b
>   s1 = replaceLemma (sym (toFrom isoA (to isoA a))) (to (isoBa a) b)
>   s2 : from (isoBa (from isoA (to isoA a))) (replace (sym (toFrom isoA (to isoA a))) (to (isoBa a) b))
>        =
>        from (isoBa a) (to (isoBa a) b)
>   s2 = depCong2' {alpha = A}
>                  {P = \ a => B' (to isoA a)}
>                  {Q = \ a => \ pa => B a}
>                  {a1 = from isoA (to isoA a)}
>                  {a2 = a}
>                  {Pa1 = replace (sym (toFrom isoA (to isoA a))) (to (isoBa a) b)}
>                  {Pa2 = to (isoBa a) b}
>                  {f = \ x => \ y => from (isoBa x) y}
>                  (fromTo isoA a)
>                  s1
>   s3 : from (isoBa a) (to (isoBa a) b) = b
>   s3 = fromTo (isoBa a) b
> %freeze isoReplaceLemma2


> |||
> sigmaIsoLemma :  (A : Type) -> (A' : Type) ->  (B : A -> Type) -> (B' : A' -> Type) ->
>                  (isoA : Iso A A') ->
>                  (isoBa  : (a : A) -> Iso (B a) (B' (to isoA a)) ) ->
>                  Iso (Sigma A B) (Sigma A' B')
> sigmaIsoLemma A A' B B' isoA isoBa = MkIso toQ fromQ toFromQ fromToQ
>   where toQ      : Sigma A  B  -> Sigma A' B'
>         toQ   (MkSigma a b)   = MkSigma (to isoA a) (to (isoBa a) b)
>
>         fromQ    : Sigma A' B' -> Sigma A  B
>         fromQ (MkSigma a' b') = (MkSigma a b) where
>           a : A
>           a = from isoA a'
>           b : B a
>           b = from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b')
>
>         toFromQ  : (ab' : Sigma A' B') -> toQ (fromQ ab') = ab'
>         toFromQ  (MkSigma a' b') = trans s1 (trans s2 s3) where
>           s1 : toQ (fromQ (MkSigma a' b'))
>                =
>                toQ (MkSigma (from isoA a') (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b')))
>           s1 = Refl
>           s2 : toQ (MkSigma (from isoA a') (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b')))
>                =
>                MkSigma (to isoA (from isoA a'))
>                        (to (isoBa (from isoA a')) (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b')))
>           s2 = Refl
>           s3 : MkSigma (to isoA (from isoA a'))
>                        (to (isoBa (from isoA a')) (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b')))
>                =
>                MkSigma a' b'
>           s3 = sigmaEqLemma2 {s1 = MkSigma (to isoA (from isoA a'))
>                                            (to (isoBa (from isoA a')) (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b')))}
>                              {s2 = MkSigma a' b'}
>                              (toFrom isoA a')
>                              (isoReplaceLemma1 isoA isoBa a' b')
>
>         fromToQ : (ab  : Sigma A B) -> fromQ (toQ ab) = ab
>         fromToQ (MkSigma a b) = trans s1 (trans s2 s3) where
>           s1 : fromQ (toQ (MkSigma a b))
>                =
>                fromQ (MkSigma (to isoA a) (to (isoBa a) b))
>           s1 = Refl
>           s2 : fromQ (MkSigma (to isoA a) (to (isoBa a) b))
>                =
>                MkSigma (from isoA (to isoA a))
>                        (from (isoBa (from isoA (to isoA a))) (replace (sym (toFrom isoA (to isoA a))) (to (isoBa a) b)))
>           s2 = Refl
>           s3 : MkSigma (from isoA (to isoA a))
>                        (from (isoBa (from isoA (to isoA a))) (replace (sym (toFrom isoA (to isoA a))) (to (isoBa a) b)))
>                =
>                MkSigma a b
>           s3 = sigmaEqLemma2 {s1 = MkSigma (from isoA (to isoA a))
>                                            (from (isoBa (from isoA (to isoA a))) (replace (sym (toFrom isoA (to isoA a))) (to (isoBa a) b)))}
>                              {s2 = MkSigma a b}
>                              (fromTo isoA a)
>                              (isoReplaceLemma2 isoA isoBa a b)
> %freeze sigmaIsoLemma


> ||| |Sigma (Fin Z) P| are void
> voidSigmaFinZ : {P : Fin Z -> Type} -> Iso (Sigma (Fin Z) P) Void
> voidSigmaFinZ = MkIso (\x => void (uninhabited x))
>                       (\x => void x)
>                       (\x => void x)
>                       (\x => void (uninhabited x))
> %freeze voidSigmaFinZ


> ||| Decomposition lemma
> sigmaEitherLemma : {n : Nat} ->
>                    {P : Fin (S n) -> Type} ->
>                    Iso (Sigma (Fin (S n)) P) (Either (P FZ) (Sigma (Fin n) (tail P)))
> sigmaEitherLemma {n} {P} = MkIso to from toFrom fromTo where
>   to :   Sigma (Fin (S n)) P -> Either (P FZ) (Sigma (Fin n) (tail P))
>   to (MkSigma FZ     j) = Left j
>   to (MkSigma (FS k) j) = Right (MkSigma k j)
>   from : Either (P FZ) (Sigma (Fin n) (tail P)) -> Sigma (Fin (S n)) P
>   from (Left j) = MkSigma FZ j
>   from (Right (MkSigma k j)) = MkSigma (FS k) j
>   toFrom : (e : Either (P FZ) (Sigma (Fin n) (tail P))) -> to (from e) = e
>   toFrom (Left j) = Refl
>   toFrom (Right (MkSigma k j)) = Refl
>   fromTo : (s : Sigma (Fin (S n)) P) -> from (to s) = s
>   fromTo (MkSigma  FZ    j) = Refl
>   fromTo (MkSigma (FS k) j) = Refl
> %freeze sigmaEitherLemma


> |||
> sigmaFinEitherLemma : {n : Nat} -> {f : Fin (S n) -> Nat} ->
>                       Iso
>                       (Sigma (Fin (S n)) (Fin . f))
>                       (Either (Fin (f FZ)) (Sigma (Fin n) (Fin . (tail f))))
> sigmaFinEitherLemma {n} {f} =
>     ( Sigma (Fin (S n)) (Fin . f)                                     )
>   ={ sigmaEitherLemma {n = n} {P = Fin . f} }=
>     ( Either (Fin (f FZ)) (Sigma (Fin n) (tail (Fin . f)))            )
>   -- ={ isoCong {P = \ X => Either (Fin (f FZ)) (Sigma (Fin n) X)} (sym (lambdaLemma1 (tail (Fin . f)))) }=
>   -- ={ isoCong {P = \ X => Either (Fin (f FZ)) (Sigma (Fin n) X)} Refl }=
>   ={ isoRefl }= 
>     ( Either (Fin (f FZ)) (Sigma (Fin n) (\ k => (tail (Fin . f)) k)) )
>   ={ isoRefl }=
>     ( Either (Fin (f FZ)) (Sigma (Fin n) (\ k => (Fin . f) (FS k)))   )
>   ={ isoRefl }=
>     ( Either (Fin (f FZ)) (Sigma (Fin n) (\ k => Fin (f (FS k))))     )
>   ={ isoRefl }=
>     ( Either (Fin (f FZ)) (Sigma (Fin n) (\ k => Fin ((tail f) k)))   )
>   ={ isoRefl }=
>     ( Either (Fin (f FZ)) (Sigma (Fin n) (\ k => (Fin . (tail f)) k)) )
>   -- ={ isoCong {P = \ X => Either (Fin (f FZ)) (Sigma (Fin n) X)} (lambdaLemma1 (Fin . (tail f))) }=
>   ={ isoRefl }= 
>     ( Either (Fin (f FZ)) (Sigma (Fin n) (Fin . (tail f)))            )
>   QED
> %freeze sigmaFinEitherLemma


> ||| |finDepPairTimes| for dependent pairs
> finDepPairTimes : {n : Nat} -> {f : Fin n -> Nat} ->
>                   Iso (Sigma (Fin n) (Fin . f))
>                       (Fin (sum f))
> finDepPairTimes {n = Z} {f} =
>     ( Sigma (Fin Z) (Fin . f)          )
>   ={ voidSigmaFinZ }=
>     ( Void                             )
>   ={ isoSym finZeroBot }=
>     ( Fin Z                            )
>   QED
> finDepPairTimes {n = S m} {f} =
>     ( Sigma (Fin (S m)) (Fin . f)                                   )
>   ={ sigmaFinEitherLemma }=
>     ( Either (Fin (f FZ)) (Sigma (Fin m) (Fin . (tail f)))          )
>   ={ eitherCongRight (finDepPairTimes {n = m} {f = tail f}) }=
>     ( Either (Fin (f FZ)) (Fin (sum (tail f)))                      )
>   ={ eitherFinPlus }=
>     ( Fin (f FZ + sum (tail f))                                     )
>   ={ isoRefl }=
>     ( Fin (sum f)                                                   )
>   QED
> %freeze finDepPairTimes

Sigma Exists properties

> |||
> sigmaExistsLemma : {A : Type} -> {P : A -> Type} ->
>                    Iso (Sigma A P) (Exists P)
> sigmaExistsLemma {A} {P} = MkIso to from toFrom fromTo where
>   to : Sigma A P -> Exists P
>   to (MkSigma _ p) = Evidence _ p
>   from : Exists P -> Sigma A P
>   from (Evidence _ p) = MkSigma _ p
>   toFrom : (e : Exists P) -> to (from e) = e
>   toFrom (Evidence _ _) = Refl
>   fromTo : (s : Sigma A P) -> from (to s) = s
>   fromTo (MkSigma _ _) = Refl
> %freeze sigmaExistsLemma


Finitess properties

> ||| For finite predicates, Sigma types of finite types are finite
> finiteSigmaLemma0 : {A : Type} -> {P : A -> Type} ->
>                     Finite A -> Finite1 P -> Finite (Sigma A P)
> finiteSigmaLemma0 {A} {P} (MkSigma n isoA) f1P = MkSigma sumf (isoTrans step1 step2)
>   where  f' : A     -> Nat
>          f' a = card (f1P a)
>          f  : Fin n -> Nat
>          f = f' . from isoA
>          sumf : Nat
>          sumf = sum f
>          step1 : Iso (Sigma A P) (Sigma (Fin n) (Fin . f))
>          step1 = sigmaIsoLemma A (Fin n) P (Fin . f) isoA s5 where -- s6 where
>            s1 : (a : A) -> Iso (P a) (Fin (f' a))
>            s1 a =  iso (f1P a)
>            s2 : (a : A) -> Iso (P a) (Fin (f' (from isoA (to isoA a))))
>            s2 a = replace {P = \ x => Iso (P a) (Fin (f' x))} prf (s1 a) where
>              prf : a = from isoA (to isoA a)
>              prf = sym (fromTo isoA a)
>            s3 : (a : A) -> Iso (P a) (Fin ((f' . (from isoA)) (to isoA a)))
>            s3 = s2
>            s4 : (a : A) -> Iso (P a) (Fin (f (to isoA a)))
>            s4 = s3
>            s5 : (a : A) -> Iso (P a) ((Fin . f) (to isoA a))
>            s5 = s4
>            -- s6 : (k : Fin n) -> Iso (P (from isoA k)) ((Fin . f) k)
>            -- s6 k = iso (f1P (from isoA k))
>          step2 : Iso (Sigma (Fin n) (Fin . f)) (Fin sumf)
>          step2 = finDepPairTimes {n} {f}
> %freeze finiteSigmaLemma0


> |||
> finiteExistsLemma : {A : Type} -> {P : A -> Type} ->
>                     Finite A -> Finite1 P -> Finite (Exists {a = A} P)
> finiteExistsLemma {A} {P} fA f1P = MkSigma n iE where
>   fS : Finite (Sigma A P)
>   fS = finiteSigmaLemma0 fA f1P
>   n  : Nat
>   n  = card fS
>   iS : Iso (Sigma A P) (Fin n)
>   iS = iso fS
>   iE : Iso (Exists {a = A} P) (Fin n)
>   iE = isoTrans (isoSym (sigmaExistsLemma {A} {P})) iS
> %freeze finiteExistsLemma


Finite  A           ~= MkSigma n (Iso A (Fin n))
Finite1 P           ~= (a : A) -> MkSigma na (Iso (P a) (Fin na))
Finite (Sigma A P)  ~= MkSigma (sum na) (Iso (Sigma A P) (Fin (sum na)))
