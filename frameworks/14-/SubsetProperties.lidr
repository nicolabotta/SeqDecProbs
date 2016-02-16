> module SubsetProperties

> import Data.Fin
> import Data.Vect
> import Control.Isomorphism


> import Decidable
> import Finite
> import Unique
> import Sigma
> import PairsOperations
> import SubsetOperations
> import VectOperations
> import VectProperties
> import FiniteOperations
> import FiniteProperties
> import FinOperations
> import IsomorphismOperations
> import IsomorphismProperties
> import Basics
> import LambdaPostulates


> %default total

> %access public export


Equality of projections:

> ||| Equality of first projections
> getWitnessPreservesEq : {A  : Type} ->
>                         {P  : A -> Type} ->
>                         {s1 : Subset A P} ->
>                         {s2 : Subset A P} ->
>                         (s1 = s2) -> (getWitness s1 = getWitness s2)
> getWitnessPreservesEq {s1 = (Element a p)} {s2 = (Element a p)} Refl = Refl


> ||| Equality of second projections
> getProofPreservesEq : {A  : Type} ->
>                       {P  : A -> Type} ->
>                       {s1 : Subset A P} ->
>                       {s2 : Subset A P} ->
>                       (s1 = s2) -> (getProof s1 = getProof s2)
> getProofPreservesEq {s1 = (Element a p)} {s2 = (Element a p)} Refl = Refl


Equality of Subset types:

> ||| Introduction
> subsetEqLemma2 : {A : Type} ->
>                  {P : A -> Type} ->
>                  {s1: Subset A P} ->
>                  {s2: Subset A P} ->
>                  (getWitness s1 = getWitness s2) ->
>                  (getProof s1 = getProof s2) ->
>                  s1 = s2
> subsetEqLemma2 {A} {P} {s1 = (Element a p)} {s2 = (Element a p)} Refl Refl = Refl

subsetEqLemma2 {A} {P} {s1 = (Element a p)} {s2 = (Element a p)} r1 r2 = Refl
subsetEqLemma2 r1 r2 = Refl


> ||| Elimination and formation
> subsetEqLemma0 : {A : Type} ->
>                  {P : A -> Type} ->
>                  (s : Subset A P) ->
>                  s = (Element (getWitness s) (getProof s))
> subsetEqLemma0 (Element a p) = Refl


> ||| Equality for singleton predicates
> subsetEqLemma1 : {A  : Type} ->
>                  {P  : A -> Type} ->
>                  (s1 : Subset A P) ->
>                  (s2 : Subset A P) ->
>                  getWitness s1 = getWitness s2 ->
>                  Unique0 (P (getWitness s1)) ->
>                  s1 = s2
> subsetEqLemma1 (Element a p) (Element a q) Refl uP = cong (uP p q)


Decidability of Subset equality:

> ||| Decidability of equality 1
> subsetDecEqLemma1 : {A : Type} ->
>                     {P : A -> Type} ->
>                     (DecEq0 A) ->
>                     (DecEq1 P) ->
>                     (s1 : Subset A P) ->
>                     (s2 : Subset A P) ->
>                     Dec (s1 = s2)
> subsetDecEqLemma1 da d1p (Element a1 pa1) (Element a2 pa2)     with (da a1 a2)
>   subsetDecEqLemma1 da d1p (Element a1 pa1) (Element a1 pa2)   | (Yes Refl) with ((d1p a1) pa1 pa2)
>     subsetDecEqLemma1 da d1p (Element a1 pa1) (Element a1 pa1) | (Yes Refl) | (Yes Refl) = Yes Refl
>     subsetDecEqLemma1 da d1p (Element a1 pa1) (Element a1 pa2) | (Yes Refl) | (No contra) = No (\ eq => contra (getProofPreservesEq eq))
>   subsetDecEqLemma1 da d1p (Element a1 pa1) (Element a2 pa2)   | (No contra) = No (\ eq => contra (getWitnessPreservesEq eq))


> ||| Decidability of equality 2
> subsetDecEqLemma2 : {A : Type} ->
>                     {P : A -> Type} ->
>                     (DecEq A) ->
>                     (Unique1 {t0 = A} P) ->
>                     (s1 : Subset A P) ->
>                     (s2 : Subset A P) ->
>                     Dec (s1 = s2)
> subsetDecEqLemma2 da p1P s1 s2 with (decEq (getWitness s1) (getWitness s2))
>   | (Yes prf)   = Yes (subsetEqLemma1 s1 s2 prf (p1P (getWitness s1)))
>   | (No contra) = No (\ eq => contra (getWitnessPreservesEq eq))


We want to show that |toVect| is complete

< toVectSubsetComplete : {A   : Type} ->
<                        {P   : A -> Type} ->
<                        (fA  : Finite A) ->
<                        (d1P : Dec1 P) ->
<                        (Unique1 {t0 = A} P) ->
<                        (s   : Subset A P) ->
<                        Elem s (getProof (toVectSubset fA d1P))

We start by deriving two auxiliary results. The first one is

> toVectSubsetLemma : {A : Type} ->
>                     {P : A -> Type} ->
>                     (fA : Finite A) ->
>                     (d1P : Dec1 P) ->
>                     (a : A) ->
>                     (p : P a) ->
>                     Elem a (map Subset.getWitness (Sigma.getProof (toVectSubset fA d1P)))
> toVectSubsetLemma {A} {P} fA d1P a p =
>   filterTagSubsetLemma d1P a (toVect fA) (toVectComplete fA a) p

The proof is computed by applying |VectProperties.filterTagSubsetLemma|:

< filterTagSubsetLemma : {A : Type} -> {P : A -> Type} ->
<                       (d1P : Dec1 P) ->
<                       (a : A) ->
<                       (as : Vect n A) ->
<                       (Elem a as) ->
<                       (p : P a) ->
<                       Elem a (map getWitness (getProof (filterTagSubset d1P as)))

to |d1P|, |a|, to the vector-based representation of |A| associated to
|fA| provided by |FiniteOperations.toVect fA| and to a proof that |a| is
an element of |FiniteOperations.toVect fA|. The latter follows from
completeness of |toVect|, see |FiniteProperties.toVectComplete|. In this
form, |toVectLemma| does not type check.

The second result is

> subsetUniqueLemma1 : {A   : Type} ->
>                      {P   : A -> Type} ->
>                      (Unique1 {t0 = A} P) ->
>                      (a : A) ->
>                      (p : P a) ->
>                      (ss : Vect n (Subset A P)) ->
>                      (Elem a (map Subset.getWitness ss)) ->
>                      Elem (Element a p) ss
> subsetUniqueLemma1 u1P a p Nil prf = absurd prf
> subsetUniqueLemma1 u1P a p ((Element a q) :: ss) (Here {x = a}) with (u1P a p q)
>   subsetUniqueLemma1 u1P a p ((Element a p) :: ss) (Here {x = a}) | Refl =
>     Here {x = (Element a p)} {xs = ss}
> subsetUniqueLemma1 u1P a1 p1 ((Element a2 p2) :: ss) (There prf) =
>   There (subsetUniqueLemma1 u1P a1 p1 ss prf)

With |toVectLemma| and |subsetUniqueLemma1|, it is easy to show that
|toVect| is complete:

> toVectSubsetComplete : {A   : Type} ->
>                        {P   : A -> Type} ->
>                        (fA  : Finite A) ->
>                        (d1P : Dec1 P) ->
>                        (Unique1 {t0 = A} P) ->
>                        (s   : Subset A P) ->
>                        Elem s (getProof (toVectSubset fA d1P))
> toVectSubsetComplete fA d1P u1P (Element a p) = s1 where
>   s0 : Elem a (map Subset.getWitness (getProof (toVectSubset fA d1P)))
>   s0 = toVectSubsetLemma fA d1P a p
>   s1 : Elem (Element a p) (getProof (toVectSubset fA d1P))
>   s1 = subsetUniqueLemma1 u1P a p (getProof (toVectSubset fA d1P)) s0


> {-
> toVectSubsetInjective1 : {A   : Type} ->
>                          {P   : A -> Type} ->
>                          (fA  : Finite A) ->
>                          (d1P : Dec1 P) ->
>                          (Unique1 {t0 = A} P) ->
>                          Injective1 (getProof (toVectSubset fA d1P))
> toVectSubsetInjective1 fA dP uP =
>   injectiveFilterTagSubsetLemma dP (toVect fA) (toVectInjective1 fA)
> -}


Subset Fin properties:

> using (P : Fin Z -> Type)
>   implementation Uninhabited (Subset (Fin Z) P) where
>     uninhabited (Element k _) = absurd k



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


> subsetIsoLemma :  (A : Type) -> (A' : Type) ->  (B : A -> Type) -> (B' : A' -> Type) ->
>                  (isoA : Iso A A') ->
>                  (isoBa  : (a : A) -> Iso (B a) (B' (to isoA a)) ) ->
>                  Iso (Subset A B) (Subset A' B')
> subsetIsoLemma A A' B B' isoA isoBa = MkIso toQ fromQ toFromQ fromToQ
>   where toQ      : Subset A  B  -> Subset A' B'
>         toQ   (Element a b)   = (Element (to isoA a) (to (isoBa a) b))
>
>         fromQ    : Subset A' B' -> Subset A  B
>         fromQ (Element a' b') = (Element a b) where
>           a : A
>           a = from isoA a'
>           b : B a
>           b = from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b')
>
>         toFromQ  : (ab' : Subset A' B') -> toQ (fromQ ab') = ab'
>         toFromQ  (Element a' b') = trans s1 (trans s2 s3) where
>           s1 : toQ (fromQ (Element a' b'))
>                =
>                toQ (Element (from isoA a') (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b')))
>           s1 = Refl
>           s2 : toQ (Element (from isoA a') (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b')))
>                =
>                Element (to isoA (from isoA a'))
>                        (to (isoBa (from isoA a')) (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b')))
>           s2 = Refl
>           s3 : Element (to isoA (from isoA a'))
>                        (to (isoBa (from isoA a')) (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b')))
>                =
>                (Element a' b')
>           s3 = subsetEqLemma2 {s1 = Element (to isoA (from isoA a'))
>                                             (to (isoBa (from isoA a')) (from (isoBa (from isoA a')) (replace (sym (toFrom isoA a')) b')))}
>                               {s2 = (Element a' b')}
>                               (toFrom isoA a')
>                               (isoReplaceLemma1 isoA isoBa a' b')
>
>         fromToQ : (ab  : Subset A  B) -> fromQ (toQ ab) = ab
>         fromToQ (Element a b) = trans s1 (trans s2 s3) where
>           s1 : fromQ (toQ (Element a b))
>                =
>                fromQ (Element (to isoA a) (to (isoBa a) b))
>           s1 = Refl
>           s2 : fromQ (Element (to isoA a) (to (isoBa a) b))
>                =
>                Element (from isoA (to isoA a))
>                        (from (isoBa (from isoA (to isoA a))) (replace (sym (toFrom isoA (to isoA a))) (to (isoBa a) b)))
>           s2 = Refl
>           s3 : Element (from isoA (to isoA a))
>                        (from (isoBa (from isoA (to isoA a))) (replace (sym (toFrom isoA (to isoA a))) (to (isoBa a) b)))
>                =
>                (Element a b)
>           s3 = subsetEqLemma2 {s1 = Element (from isoA (to isoA a))
>                                             (from (isoBa (from isoA (to isoA a))) (replace (sym (toFrom isoA (to isoA a))) (to (isoBa a) b)))}
>                               {s2 = (Element a b)}
>                               (fromTo isoA a)
>                               (isoReplaceLemma2 isoA isoBa a b)


> ||| |Subset (Fin Z) P| are void
> voidSubsetFinZ : {P : Fin Z -> Type} -> Iso (Subset (Fin Z) P) Void
> voidSubsetFinZ = MkIso (\x => void (uninhabited x))
>                       (\x => void x)
>                       (\x => void x)
>                       (\x => void (uninhabited x))


> ||| Decomposition lemma
> subsetEitherLemma : {n : Nat} ->
>                    {P : Fin (S n) -> Type} ->
>                    Iso (Subset (Fin (S n)) P) (Either (P FZ) (Subset (Fin n) (tail P)))
> subsetEitherLemma {n} {P} = MkIso to from toFrom fromTo where
>   to :   Subset (Fin (S n)) P -> Either (P FZ) (Subset (Fin n) (tail P))
>   to (Element FZ j) = Left j
>   to (Element (FS k) j) = Right (Element k j)
>   from : Either (P FZ) (Subset (Fin n) (tail P)) -> Subset (Fin (S n)) P
>   from (Left j) = (Element FZ j)
>   from (Right (Element k j)) = (Element (FS k) j)
>   toFrom : (e : Either (P FZ) (Subset (Fin n) (tail P))) -> to (from e) = e
>   toFrom (Left j) = Refl
>   toFrom (Right (Element k j)) = Refl
>   fromTo : (s : Subset (Fin (S n)) P) -> from (to s) = s
>   fromTo (Element FZ j) = Refl
>   fromTo (Element (FS k) j) = Refl


> subsetFinEitherLemma : {n : Nat} -> {f : Fin (S n) -> Nat} ->
>                       Iso
>                       (Subset (Fin (S n)) (Fin . f))
>                       (Either (Fin (f FZ)) (Subset (Fin n) (Fin . (tail f))))
> subsetFinEitherLemma {n} {f} =
>     ( Subset (Fin (S n)) (Fin . f)                                     )
>   ={ subsetEitherLemma {n = n} {P = Fin . f} }=
>     ( Either (Fin (f FZ)) (Subset (Fin n) (tail (Fin . f)))            )
>   -- ={ isoCong {P = \ X => Either (Fin (f FZ)) (Subset (Fin n) X)} (sym (lambdaLemma1 (tail (Fin . f)))) }=
>   ={ isoRefl }=
>     ( Either (Fin (f FZ)) (Subset (Fin n) (\ k => (tail (Fin . f)) k)) )
>   ={ isoRefl }=
>     ( Either (Fin (f FZ)) (Subset (Fin n) (\ k => (Fin . f) (FS k)))   )
>   ={ isoRefl }=
>     ( Either (Fin (f FZ)) (Subset (Fin n) (\ k => Fin (f (FS k))))     )
>   ={ isoRefl }=
>     ( Either (Fin (f FZ)) (Subset (Fin n) (\ k => Fin ((tail f) k)))   )
>   ={ isoRefl }=
>     ( Either (Fin (f FZ)) (Subset (Fin n) (\ k => (Fin . (tail f)) k)) )
>   -- ={ isoCong {P = \ X => Either (Fin (f FZ)) (Subset (Fin n) X)} (lambdaLemma1 (Fin . (tail f))) }=
>   ={ isoRefl }=
>     ( Either (Fin (f FZ)) (Subset (Fin n) (Fin . (tail f)))            )
>   QED


> ||| |finDepPairTimes| for dependent pairs
> finDepPairTimes : {n : Nat} -> {f : Fin n -> Nat} ->
>                   Iso (Subset (Fin n) (Fin . f))
>                       (Fin (sum f))
> finDepPairTimes {n = Z} {f} =
>     ( Subset (Fin Z) (Fin . f)          )
>   ={ voidSubsetFinZ }=
>     ( Void                             )
>   ={ isoSym finZeroBot }=
>     ( Fin Z                            )
>   QED
> finDepPairTimes {n = S m} {f} =
>     ( Subset (Fin (S m)) (Fin . f)                                   )
>   ={ subsetFinEitherLemma }=
>     ( Either (Fin (f FZ)) (Subset (Fin m) (Fin . (tail f)))          )
>   ={ eitherCongRight (finDepPairTimes {n = m} {f = tail f}) }=
>     ( Either (Fin (f FZ)) (Fin (sum (tail f)))                      )
>   ={ eitherFinPlus }=
>     ( Fin (f FZ + sum (tail f))                                     )
>   ={ isoRefl }=
>     ( Fin (sum f)                                                   )
>   QED


Subset Exists properties

> subsetExistsLemma : {A : Type} -> {P : A -> Type} ->
>                    Iso (Subset A P) (Exists P)
> subsetExistsLemma {A} {P} = MkIso to from toFrom fromTo where
>   to : Subset A P -> Exists P
>   to (Element _ p) = Evidence _ p
>   from : Exists P -> Subset A P
>   from (Evidence _ p) = Element _ p
>   toFrom : (e : Exists P) -> to (from e) = e
>   toFrom (Evidence _ _) = Refl
>   fromTo : (s : Subset A P) -> from (to s) = s
>   fromTo (Element _ _) = Refl


Finitess properties

> ||| For finite predicates, Subset types of finite types are finite
> finiteSubsetLemma0 : {A : Type} -> {P : A -> Type} ->
>                     Finite A -> Finite1 P -> Finite (Subset A P)
> finiteSubsetLemma0 {A} {P} (Evidence n isoA) f1P = Evidence sumf (isoTrans step1 step2)
>   where  f' : A     -> Nat
>          f' a = card (f1P a)
>          f  : Fin n -> Nat
>          f = f' . from isoA
>          sumf : Nat
>          sumf = sum f
>          step1 : Iso (Subset A P) (Subset (Fin n) (Fin . f))
>          step1 = subsetIsoLemma A (Fin n) P (Fin . f) isoA s5 where -- s6 where
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
>          step2 : Iso (Subset (Fin n) (Fin . f)) (Fin sumf)
>          step2 = finDepPairTimes {n} {f}


> finiteExistsLemma : {A : Type} -> {P : A -> Type} ->
>                     Finite A -> Finite1 P -> Finite (Exists {a = A} P)
> finiteExistsLemma {A} {P} fA f1P = Evidence n iE where
>   fS : Finite (Subset A P)
>   fS = finiteSubsetLemma0 fA f1P
>   n  : Nat
>   n  = card fS
>   iS : Iso (Subset A P) (Fin n)
>   iS = iso fS
>   iE : Iso (Exists {a = A} P) (Fin n)
>   iE = isoTrans (isoSym (subsetExistsLemma {A} {P})) iS


Finite  A           ~= (n ** Iso A (Fin n))
Finite1 P           ~= (a : A) -> (na ** Iso (P a) (Fin na))
Finite (Subset A P)  ~= (sum na ** Iso (Subset A P) (Fin (sum na)))
