> import Data.Fin
> import Data.Vect
> import Data.Vect.Quantifiers
> import Syntax.PreorderReasoning
> import Control.Isomorphism

> %default total

> namespace Util
>   pair : (a -> b, a -> c) -> a -> (b, c)
>   pair (f, g) x = (f x, g x)

> namespace TotalPreorder
>   data TotalPreorder : Type -> Type where
>     MkTotalPreorder : {A : Type} -> 
>                       (R : A -> A -> Type) ->
>                       (reflexive : (x : A) -> R x x) ->
>                       (transitive : (x : A) -> (y : A) -> (z : A) -> R x y -> R y z -> R x z) ->
>                       (either : (x : A) -> (y : A) -> Either (R x y) (R y x)) ->
>                       TotalPreorder A

> namespace NatProperties
>   instance Uninhabited (S n = Z) where                                                                                      
>     uninhabited Refl impossible  
>   idSuccPreservesLTE : (m : Nat) -> (n : Nat) -> m `LTE` n -> m `LTE` (S n)
>   idSuccPreservesLTE  Z     n    prf = LTEZero
>   idSuccPreservesLTE (S m)  Z    prf = absurd prf
>   idSuccPreservesLTE (S m) (S n) prf = LTESucc (idSuccPreservesLTE m n (fromLteSucc prf))
>   ltZS : (m : Nat) -> LT Z (S m)
>   ltZS  Z    = LTESucc LTEZero 
>   ltZS (S m) = idSuccPreservesLTE (S Z) (S m) (ltZS m)
>   notZisgtZ : Not (n = Z) -> LT Z n
>   notZisgtZ {n = Z}   contra = void (contra Refl) 
>   notZisgtZ {n = S m} _      = ltZS m
>   gtZisnotZ : LT Z n -> Not (n = Z)
>   gtZisnotZ {n = Z}   p = absurd p
>   gtZisnotZ {n = S m} p = \ neqZ => absurd neqZ
>   reflexiveLTE : (n : Nat) -> LTE n n
>   reflexiveLTE n = lteRefl {n}
>   transitiveLTE : (m : Nat) -> (n : Nat) -> (o : Nat) ->
>                   LTE m n -> LTE n o -> LTE m o
>   transitiveLTE  Z       n     o   LTEZero                 nlteo  = LTEZero
>   transitiveLTE (S m) (S n) (S o) (LTESucc mlten) (LTESucc nlteo) = LTESucc (transitiveLTE m n o mlten nlteo)
>   totalLTE : (m : Nat) -> (n : Nat) -> Either (LTE m n) (LTE n m)
>   totalLTE  Z    n     = Left LTEZero
>   totalLTE (S m) Z     = Right LTEZero
>   totalLTE (S m) (S n) with (totalLTE m n)
>     | (Left  p) = Left  (LTESucc p)
>     | (Right p) = Right (LTESucc p)
>   totalPreorderNatLTE : TotalPreorder Nat
>   totalPreorderNatLTE = 
>     MkTotalPreorder LTE reflexiveLTE transitiveLTE totalLTE

> namespace FinOperations
>   tail : {A : Type} -> (Fin (S n) -> A) -> (Fin n -> A)
>   tail f k = f (FS k)
>   toVect : {A : Type} -> (Fin n -> A) -> Vect n A
>   toVect {n =   Z} _ = Nil
>   toVect {n = S m} f = (f FZ) :: (toVect (tail f)) 

> namespace FinProperties
>   toVectComplete : {A : Type} -> (f : Fin n -> A) -> (k : Fin n) -> Elem (f k) (toVect f)
>   toVectComplete {n = Z} _  k     = void (uninhabited k)
>   toVectComplete         f  FZ    = Here
>   toVectComplete         f (FS j) = There (toVectComplete (tail f) j)

> namespace TotalPreorderOperations
>   R : {A : Type} -> TotalPreorder A -> (A -> A -> Type)
>   R (MkTotalPreorder R _ _ _) = R
>   reflexive : {A : Type} -> 
>               (tp : TotalPreorder A) -> 
>               (x : A) -> (R tp) x x
>   reflexive (MkTotalPreorder _ reflexive _ _) = reflexive
>   transitive : {A : Type} -> 
>                (tp : TotalPreorder A) -> 
>                (x : A) -> (y : A) -> (z : A) -> (R tp) x y -> (R tp) y z -> (R tp) x z
>   transitive (MkTotalPreorder _ _ transitive _) = transitive
>   either : {A : Type} -> 
>            (tp : TotalPreorder A) -> 
>            (x : A) -> (y : A) -> Either ((R tp) x y) ((R tp) y x)
>   either (MkTotalPreorder _ _ _ either) = either
>   from2 : {A, B : Type} -> (B -> B -> Type) -> (A, B) -> (A, B) -> Type
>   from2 R x y = R (snd x) (snd y)
>   fromTotalPreorder2 : {A, B : Type} -> TotalPreorder B -> TotalPreorder (A, B)
>   fromTotalPreorder2 to = 
>     MkTotalPreorder (from2 (R to))
>                     (\ x => reflexive to (snd x))
>                     (\ x => \ y => \ z => \ xRy => \ yRz => transitive to (snd x) (snd y) (snd z) xRy yRz)
>                     (\ x => \ y => either to (snd x) (snd y))

> namespace VectOperations
>   argmaxMax : {A : Type} -> 
>               TotalPreorder A -> Vect n A -> LT Z n -> (Fin n, A)
>   argmaxMax {n = Z}       tp  Nil                p = absurd p
>   argmaxMax {n = S Z}     tp (a :: Nil)          _ = (FZ, a)
>   argmaxMax {n = S (S m)} tp (a' :: (a'' :: as)) _ with (argmaxMax tp (a'' :: as) (ltZS m))
>     | (k, max) with (either tp a' max)
>       | (Left  _) = (FS k, max)
>       | (Right _) = (FZ, a')
>   max : {A : Type} -> 
>         TotalPreorder A -> Vect n A -> LT Z n -> A
>   max tp as p = snd (argmaxMax tp as p)

> namespace VectProperties
>   instance Uninhabited (Elem {a} x Nil) where
>     uninhabited Here impossible                                                                                          
>     uninhabited (There p) impossible      
>   elemLemma : {A : Type} -> {n : Nat} -> 
>               (a : A) -> (as : Vect n A) ->
>               Elem a as -> LT Z n
>   elemLemma {n = Z}   a Nil p = absurd p
>   elemLemma {n = S m} a as  p = ltZS m
>   AnyExistsLemma : {A : Type} -> {P : A -> Type} -> Any P as -> Exists P
>   AnyExistsLemma (Here {x} px) = Evidence x px 
>   AnyExistsLemma (There prf) = AnyExistsLemma prf
>   ElemAnyLemma : {A : Type} -> {P : A -> Type} -> P a -> Elem a as -> Any P as
>   ElemAnyLemma p Here = Here p
>   ElemAnyLemma p (There e) = There (ElemAnyLemma p e)
>   mapLemma : {A, B : Type} -> (as : Vect n A) -> (f : A -> B) ->
>              (a : A) -> Elem a as -> Elem (f a) (map f as)
>   mapLemma  Nil      f a aeas = absurd aeas
>   mapLemma (a :: as) f a   Here       = Here
>   mapLemma (a :: as) f a' (There prf) = There (mapLemma as f a' prf)
>   maxLemma : {A : Type} -> 
>              (tp : TotalPreorder A) -> 
>              (a : A) -> (as : Vect n A) -> (p : LT Z n) -> a `Elem` as -> 
>              R tp a (max tp as p)
>   maxLemma {n = Z}       tp a        Nil          p  _          = absurd p
>   maxLemma {n = S Z}     tp a (a  :: Nil)         _  Here       = reflexive tp a
>   maxLemma {n = S Z}     tp a (a' :: Nil)         _ (There prf) = absurd prf
>   maxLemma {n = S (S m)} tp a (a :: (a'' :: as))  _  Here with (argmaxMax tp (a'' :: as) (ltZS m))
>     | (k, max) with (either tp a max)
>       | (Left  p) = p
>       | (Right _) = reflexive tp a
>   maxLemma {n = S (S m)} tp a (a' :: (a'' :: as)) _ (There prf) with (argmaxMax tp (a'' :: as) (ltZS m)) proof itsEqual
>     | (k, max) with (either tp a' max)
>       | (Left  _) = replace {P = \rec => R tp a (snd rec)} 
>                             (sym itsEqual) 
>                             (maxLemma {n = S m} tp a (a'' :: as) (ltZS m) prf)
>       | (Right p) = s3 where
>         s1 : R tp a (snd (VectOperations.argmaxMax tp (a'' :: as) (ltZS m)))
>         s1 = maxLemma {n = S m} tp a (a'' :: as) (ltZS m) prf
>         s2 : R tp (snd (VectOperations.argmaxMax tp (a'' :: as) (ltZS m))) a'
>         s2 = replace {P = \rec => R tp (snd rec) a'} itsEqual p
>         s3 : R tp a a'
>         s3 = transitive tp a (snd (VectOperations.argmaxMax tp (a'' :: as) (ltZS m))) a' s1 s2

> namespace IsomorphismOperations
>   to : {A, B : Type} -> Iso A B -> (A -> B)
>   to (MkIso to from toFrom fromTo) = to
>   from : {A, B : Type} -> Iso A B -> (B -> A)
>   from (MkIso to from toFrom fromTo) = from
>   toFrom : {A, B : Type} -> (iso : Iso A B) -> (b : B) -> to iso (from iso b) = b
>   toFrom (MkIso to from toFrom fromTo) = toFrom
>   fromTo : {A, B : Type} -> (iso : Iso A B) -> (a : A) -> from iso (to iso a) = a
>   fromTo (MkIso to from toFrom fromTo) = fromTo

> namespace Finite
>   Finite : Type -> Type
>   Finite A = Exists (\ n => Iso A (Fin n))

> namespace FiniteOperations
>   card : {A : Type} -> (fA : Finite A) -> Nat
>   card = getWitness 
>   toVect : {A : Type} -> (fA : Finite A) -> Vect (card fA) A
>   toVect (Evidence n iso) = toVect (from iso)
>   Empty : {A : Type} -> Finite A -> Type
>   Empty fA = card fA = Z
>   NonEmpty : {A : Type} -> Finite A -> Type
>   NonEmpty = Not . Empty

> namespace FiniteProperties
>   toVectComplete : {A : Type} -> (fA : Finite A) -> (a : A) -> Elem a (toVect fA)
>   toVectComplete (Evidence n iso) a = s3 where
>     s1  :  Elem (from iso (to iso a)) (toVect (from iso))
>     s1  =  toVectComplete (from iso) (to iso a) 
>     s2  :  from iso (to iso a) = a
>     s2  =  fromTo iso a
>     s3  :  Elem a (toVect (from iso))
>     s3  =  replace {P = \ z => Elem z (toVect (from iso))} s2 s1
>   nonEmptyLemma : {A : Type} -> (fA : Finite A) -> A -> NonEmpty fA
>   nonEmptyLemma fA a = gtZisnotZ (elemLemma {n = card fA} a (toVect fA) (toVectComplete fA a))

> namespace Opt
>   optargmaxMax : {A, B : Type} -> 
>                  TotalPreorder B -> 
>                  (fA : Finite A) -> (ne : NonEmpty fA) -> 
>                  (f : A -> B) -> (A,B)
>   optargmaxMax {A} {B} tp fA nefA f = max (fromTotalPreorder2 tp) abs ltZn where
>     n    : Nat
>     n    = card fA
>     ltZn : LT Z n
>     ltZn = notZisgtZ nefA
>     abs  : Vect n (A,B)
>     abs  = map (pair (id, f)) (toVect fA)
>   optmax : {A, B : Type} ->
>            TotalPreorder B -> 
>            (fA : Finite A) -> (ne : NonEmpty fA) -> 
>            (f : A -> B) -> B
>   optmax tp fA nefA f = snd (optargmaxMax tp fA nefA f)
>   optmaxSpec : {A, B : Type} -> 
>                (tp : TotalPreorder B) -> 
>                (fA : Finite A) -> (nefA : NonEmpty fA) -> 
>                (f : A -> B) ->
>                (a : A) -> R tp (f a) (optmax tp fA nefA f)
>   optmaxSpec {A} {B} tp fA nefA f a = s4 where
>     n    : Nat
>     n    = card fA
>     ltZn : LT Z n
>     ltZn = notZisgtZ nefA
>     abs  : Vect n (A,B)
>     abs  = map (pair (id, f)) (toVect fA)
>     s1   : Elem (a, f a) abs
>     s1   = mapLemma (toVect fA) (pair (id, f)) a (toVectComplete fA a)
>     s2   : (from2 (R tp)) (a, f a) (max (fromTotalPreorder2 tp) abs ltZn) 
>     s2   = maxLemma (fromTotalPreorder2 tp) (a, f a) abs ltZn s1
>     s3   : R tp (f a) (snd (max (fromTotalPreorder2 tp) abs ltZn))
>     s3   = s2
>     s4   : R tp (f a) (optmax tp fA nefA f)
>     s4   = s3

> namespace Lala
>   M        : Type -> Type
>   Elem     : {A : Type} -> A -> M A -> Type
>   All      : {A : Type} -> (P : A -> Type) -> M A -> Type
>   X        : (t : Nat) -> Type
>   Y        : (t : Nat) -> (x : X t) -> Type
>   step     : (t : Nat) -> (x : X t) -> (y : Y t x) -> M (X (S t))
>   Pred      : X t -> X (S t) -> Type
>   Pred {t} x x'  =  Exists (\ y => x' `Elem` step t x y)
>   Viable    : (n : Nat) -> X t -> Type
>   Viable {t}  Z    _  =  ()
>   Viable {t} (S m) x  =  Exists (\ y => Lala.All (Viable m) (step t x y))
>   Reachable : X t' -> Type
>   Reachable {t' =   Z} _   =  ()
>   Reachable {t' = S t} x'  =  Exists (\ x => (Reachable x, x `Pred` x'))
>   max    : (t : Nat) -> (x : X t) -> Viable (S n) x ->
>            (f : Sigma (Y t x) (\ y => Lala.All (Viable n) (step t x y)) -> Nat) ->
>            Nat
>   maxSpec     :  (t : Nat) -> (x : X t) -> (v : Viable (S n) x) ->
>                  (f : Sigma (Y t x) (\ y => Lala.All (Viable n) (step t x y)) -> Nat) ->
>                  (s : Sigma (Y t x) (\ y => Lala.All (Viable n) (step t x y))) ->
>                  (f s) `LTE` (max t x v f)
>   fYAV : (t : Nat) -> (n : Nat) -> (x : X t) -> Viable (S n) x ->
>          Finite (Sigma (Y t x) (\ y => All (Viable {t = S t} n) (step t x y)))
>   neYAV : (t : Nat) -> (n : Nat) -> (x : X t) -> (v : Viable {t = t} (S n) x) ->
>           NonEmpty (fYAV t n x v)
>   neYAV t n x (Evidence y v) = 
>     nonEmptyLemma {A = Sigma (Y t x) (\ y => All (Viable {t = S t} n) (step t x y))} 
>                   (fYAV t n x (Evidence y v)) 
>                   (y ** v)
>   max     {n} t x v  =  
>     optmax totalPreorderNatLTE (fYAV t n x v) (neYAV t n x v)
>   maxSpec {n} t x v f s = 
>     optmaxSpec totalPreorderNatLTE (fYAV t n x v) (neYAV t n x v) f s

