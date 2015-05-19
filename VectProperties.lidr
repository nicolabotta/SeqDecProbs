> module VectProperties


> import Data.Vect
> -- import Data.VectType
> import Data.Vect.Quantifiers
> import Data.Fin
> -- import Syntax.PreorderReasoning

> import Prop
> import VectOperations
> import Decidable
> import TotalPreorder
> import TotalPreorderOperations
> import NatProperties
> -- import FinOperations
> import FinProperties
> import FunOperations


> %default total


> instance Uninhabited (Elem {a} x Nil) where
>   uninhabited Here impossible
>   uninhabited (There p) impossible


Injectivity (of |flip index|):

> ||| Injectivity (one direction)
> Injective1 : Vect n t -> Type
> Injective1 {n} xs = (i : Fin n) -> (j : Fin n) -> index i xs = index j xs -> i = j


> ||| Injectivity (the other direction)
> Injective2 : Vect n t -> Type
> Injective2 {n} xs = (i : Fin n) -> (j : Fin n) -> Not (i = j) -> Not (index i xs = index j xs)


> ||| Injective1 implies Injective2
> injectiveLemma : (xs : Vect n t) -> Injective1 xs -> Injective2 xs
> injectiveLemma xs i1xs i j contra = contra . (i1xs i j)


> ||| Tail preserves injectivity (one direction)
> injectiveTailLemma1 : (xs : Vect (S n) t) -> Injective1 xs -> Injective1 (tail xs)
> injectiveTailLemma1  Nil      p _ _ _ impossible
> injectiveTailLemma1 (x :: xs) p i j q = FSInjective i j (p (FS i) (FS j) q') where
>   q' : index (FS i) (x :: xs) = index (FS j) (x :: xs)
>   q' = q


> ||| Tail preserves injectivity (the other direction)
> injectiveTailLemma2 : (xs : Vect (S n) t) -> Injective2 xs -> Injective2 (tail xs)
> injectiveTailLemma2  Nil      p _ _ _ impossible
> injectiveTailLemma2 (x :: xs) p i j q = p (FS i) (FS j) (fsInjective2 i j q)


Indexing and lookup

> indexLemma : (k : Fin n) -> (xs : Vect n t) -> Elem (index k xs) xs
> indexLemma {n = Z}       k   Nil      = absurd k
> indexLemma {n = S m}  FZ    (x :: xs) = Here
> indexLemma {n = S m} (FS k) (x :: xs) = There (indexLemma k xs)

> indexLookupLemma : (x : alpha) ->
>                    (xs : Vect n alpha) ->
>                    (prf : Elem x xs) ->
>                    index (lookup x xs prf) xs = x
> indexLookupLemma x  Nil        prf        = absurd prf
> indexLookupLemma x (x :: xs)   Here       = Refl
> indexLookupLemma x (x' :: xs) (There prf) =
>   let ih = indexLookupLemma x xs prf in rewrite ih in Refl
> {-
> indexLookupLemma x (x' :: xs) (There prf) = trans s1 (trans s2 s3) where
>   s1 : index (lookup x (x' :: xs) (There prf)) (x' :: xs)
>        =
>        index (FS (lookup x xs prf)) (x' :: xs)
>   s1 = Refl
>   s2 : index (FS (lookup x xs prf)) (x' :: xs)
>        =
>        index (lookup x xs prf) xs
>   s2 = Refl
>   s3 : index (lookup x xs prf) xs
>        =
>        x
>   s3 = indexLookupLemma x xs prf
> -}


> |||
> lookupIndexLemma : (k : Fin n) ->
>                    (xs : Vect n t) ->
>                    (p : Injective2 xs) ->
>                    (q : Elem (index k xs) xs) ->
>                    lookup (index k xs) xs q = k
> lookupIndexLemma  FZ     Nil      _  _        impossible
> lookupIndexLemma  FZ    (x :: xs) p  Here     = Refl
> lookupIndexLemma  FZ    (x :: xs) p (There q) = s5 where
>   s1 : Not (FZ = lookup x (x :: xs) (There q))
>   s1 Refl impossible
>   s2 : index FZ (x :: xs) = x
>   s2 = Refl
>   s3 : index (lookup x (x :: xs) (There q)) (x :: xs) = x
>   s3 = indexLookupLemma x (x :: xs) (There q)
>   s4 : index FZ (x :: xs) = index (lookup x (x :: xs) (There q)) (x :: xs)
>   s4 = trans s2 (sym s3)
>   s5 : lookup (index FZ (x :: xs)) (x :: xs) (There q) = FZ
>   s5 = void ((p FZ (lookup x (x :: xs) (There q)) s1) s4)
> lookupIndexLemma (FS k)  Nil      _  _        impossible
> lookupIndexLemma (FS k) (_ :: xs) p  Here     = s5 where
>   s1 : Not (FZ = FS k)
>   s1 Refl impossible
>   s2 : index FZ ((index k xs) :: xs) = index (FS k) ((index k xs) :: xs)
>   s2 = Refl
>   s5 : lookup (index (FS k) ((index k xs) :: xs)) ((index k xs) :: xs) Here = (FS k)
>   s5 = void ((p FZ (FS k) s1) s2)
> lookupIndexLemma (FS k) (x :: xs) p (There q) =
>   let p' = injectiveTailLemma2 (x :: xs) p in
>   let ih = lookupIndexLemma k xs p' q in
>   rewrite ih in Refl


> |||
> -- indexToVectLemma : {A : Type} -> (f : Fin n -> A) -> (k : Fin n) -> f k = index k (toVect f)


Membership, quantifiers:

> ||| Membership => non emptyness
> elemLemma : {A : Type} -> {n : Nat} ->
>             (a : A) -> (as : Vect n A) ->
>             Elem a as -> LT Z n
> elemLemma {n = Z}   a Nil p = absurd p
> elemLemma {n = S m} a as  p = ltZS m


> AnyExistsLemma : {A : Type} -> {P : A -> Prop} -> {as : Vect n A} ->
>                  Any P as -> Exists P
> AnyExistsLemma (Here px) = Evidence _ px
> AnyExistsLemma (There prf) = AnyExistsLemma prf

> ElemAnyLemma : {A : Type} -> {P : A -> Prop} -> P a -> Elem a as -> Any P as
> ElemAnyLemma p Here = Here p
> ElemAnyLemma p (There e) = There (ElemAnyLemma p e)

> decAny : {A : Type} -> {P : A -> Prop} -> Dec1 P -> Dec1 (Any P)
> decAny d1P = any d1P


Container monad properties

> mapLemma : {A, B : Type} -> (as : Vect n A) -> (f : A -> B) ->
>            (a : A) -> Elem a as -> Elem (f a) (map f as)
> mapLemma  Nil      f a aeas = absurd aeas
> mapLemma (a :: as) f a   Here       = Here
> mapLemma (a :: as) f a' (There prf) = There (mapLemma as f a' prf)


> mapIdfLemma : {A, B : Type} -> (as : Vect n A) -> (f : A -> B) ->
>               (ab : (A,B)) -> Elem ab (map (pair (id,f)) as) ->
>               f (fst ab) = snd ab
> mapIdfLemma  Nil      f  ab     p        = absurd p
> mapIdfLemma (a :: as) f (a, _)  Here     = Refl
> mapIdfLemma (a :: as) f  ab    (There p) = mapIdfLemma as f ab p


Filtering

> ||| |filter| preserves membership
> filterLemma : {A : Type} ->
>               {P : A -> Type} ->
>               (d1P : Dec1 P) ->
>               (a : A) ->
>               (as : Vect n A) ->
>               Elem a as ->
>               (p : P a) ->
>               Elem a (getProof (filter d1P as))
> filterLemma d1P a   Nil       prf  p = absurd prf
> filterLemma d1P a1 (a1 :: as) Here p with (filter d1P as)
>   | (n ** as') with (d1P a1)
>     | (Yes _) = Here {x = a1} {xs = as'}
>     | (No  contra) = void (contra p)
> filterLemma {A} {P} d1P a1 (a2 :: as) (There prf) p with (filter d1P as) proof itsEqual
>   | (n ** as') with (d1P a2)
>     | (Yes _) = -- There {x = a1} {xs = as'} {y = a2} (filterLemma d1P a1 as prf p)
>                 There {x = a1} {xs = as'} {y = a2} $
>                   replace {P = \rec => Elem a1 (getProof rec)} (sym itsEqual) $
>                     filterLemma {A} {P} d1P a1 as prf p
>     | (No  _) = -- filterLemma {A} {P} d1P a1 as prf p
>                 replace {P = \rec => Elem a1 (getProof rec)} (sym itsEqual) $
>                   filterLemma {P = P} d1P a1 as prf p


> ||| |filterTag| preserves membership
> filterTagLemma : {A : Type} ->
>                  {P : A -> Type} ->
>                  {n : Nat} ->
>                  (d1P : Dec1 P) ->
>                  (a : A) ->
>                  (as : Vect n A) ->
>                  Elem a as ->
>                  (p : P a) ->
>                  Elem a (map getWitness (getProof (filterTag d1P as)))
> filterTagLemma d1P a   Nil       prf  p = absurd prf
> filterTagLemma d1P a1 (a1 :: as) Here p with (filterTag d1P as)
>   | (n ** aps') with (d1P a1)
>     | (Yes _) = Here {x = a1} {xs = map getWitness aps'}
>     | (No  contra) = void (contra p)
> filterTagLemma d1P a1 (a2 :: as) (There prf) p with (filterTag d1P as) proof itsEqual
>   | (n ** aps') with (d1P a2)
>     | (Yes _) = -- There {x = a1} {xs = map getWitness aps'} {y = a2} (filterTagLemma d1P a1 as prf p)
>                 There {x = a1} {xs = map getWitness aps'} {y = a2} $
>                   replace {P = \rec => Elem a1 (map Sigma.getWitness (getProof rec))} (sym itsEqual) $
>                     filterTagLemma d1P a1 as prf p
>     | (No  _) = -- filterTagLemma d1P a1 as prf p
>                 replace {P = \rec => Elem a1 (map Sigma.getWitness (getProof rec))} (sym itsEqual) $
>                   filterTagLemma d1P a1 as prf p

> {- Just commented out for testing
> ||| |filter| preserves injectivity
> injectiveFilterLemma : {A : Type} ->
>                        {P : A -> Type} ->
>                        {n : Nat} ->
>                        (dP : Dec1 P) ->
>                        (as : Vect n A) ->
>                        Injective1 as ->
>                        Injective1 (getProof (filter dP as))
> -}
> {-
>     = s0 where
>   n'  : Nat
>   n'  = getWitness (filter dP (a :: as))
>   as' : Vect n' A
>   as' = getProof (filter dP (a :: as))
>   s0 : Injective1 (getProof (filter dP (a :: as)))
>   s0 i j q with (filter dP as)
>     | (n' ** as') with (dP a)
>       | (Yes _) = ?liko
>       | (No  _) = s5 where
>         s5 : i = j
>         s5 = ?lala -- injectiveFilterLemma dP as (injectiveTailLemma1 (a :: as) iaas) i j q
> -}


> ||| |filterTag| preserves injectivity
> injectiveFilterTagLemma : {A : Type} ->
>                           {P : A -> Type} ->
>                           (dP : Dec1 P) ->
>                           (as : Vect n A) ->
>                           Injective1 as ->
>                           Injective1 (getProof (filterTag d1P as))
> injectiveFilterTagLemma {n = Z}   dP Nil i1as i j p = absurd i


Max and argmax

> |||
> maxLemma : {A : Type} ->
>            (tp : TotalPreorder A) ->
>            (a : A) -> (as : Vect n A) -> (p : LT Z n) -> a `Elem` as ->
>            R tp a (max tp as p)
> maxLemma {n = Z}       tp a        Nil          p  _          = absurd p
> maxLemma {n = S Z}     tp a (a  :: Nil)         _  Here       = reflexive tp a
> maxLemma {n = S Z}     tp a (a' :: Nil)         _ (There prf) = absurd prf
> maxLemma {n = S (S m)} tp a (a :: (a'' :: as))  _  Here with (argmaxMax tp (a'' :: as) (ltZS m))
>   | (k, max) with (totalPre tp a max)
>     | (Left  p) = p
>     | (Right _) = reflexive tp a
> maxLemma {n = S (S m)} tp a (a' :: (a'' :: as)) _ (There prf) with (argmaxMax tp (a'' :: as) (ltZS m)) proof itsEqual
>   | (k, max) with (totalPre tp a' max)
>     | (Left  _) = replace {P = \rec => R tp a (snd rec)}
>                           (sym itsEqual)
>                           (maxLemma {n = S m} tp a (a'' :: as) (ltZS m) prf)
>     | (Right p) = s3 where
>       s1 : R tp a (snd (VectOperations.argmaxMax tp (a'' :: as) (ltZS m)))
>       s1 = maxLemma {n = S m} tp a (a'' :: as) (ltZS m) prf
>       s2 : R tp (snd (VectOperations.argmaxMax tp (a'' :: as) (ltZS m))) a'
>       s2 = replace {P = \rec => R tp (snd rec) a'} itsEqual p
>       s3 : R tp a a'
>       s3 = transitive tp a (snd (VectOperations.argmaxMax tp (a'' :: as) (ltZS m))) a' s1 s2


> |||
> %assert_total
> argmaxLemma : {A : Type} ->
>               (tp : TotalPreorder A) ->
>               (as : Vect n A) -> (p : LT Z n) ->
>               index (argmax tp as p) as = max tp as p
> argmaxLemma {n = Z}       tp  Nil              p = absurd p
> argmaxLemma {n = S Z}     tp (a :: Nil)        p = Refl
> argmaxLemma {n = S (S m)} tp (a' :: (a'' :: as)) p with (argmaxMax tp (a'' :: as) (ltZS m)) proof itsEqual
>   | (k, max') with (totalPre tp a' max')
>     | (Left   _) = replace {P = \rec => Data.VectType.Vect.index (fst rec) (a'' :: as) = snd rec}
>                            (sym itsEqual)
>                            (argmaxLemma tp (a'' :: as) (ltZS m))
>     | (Right  _) = Refl


> |||
> %assert_total
> maxElemLemma : {A : Type} ->
>                (tp : TotalPreorder A) ->
>                (as : Vect n A) -> (p : LT Z n) ->
>                Elem (max tp as p) as
> maxElemLemma {n = Z}       tp  Nil                p = absurd p
> maxElemLemma {n = S Z}     tp (a :: Nil)          p = Here
> maxElemLemma {n = S (S m)} tp (a' :: (a'' :: as)) p with (argmaxMax tp (a'' :: as) (ltZS m)) proof itsEqual
>   | (k, max) with (totalPre tp a' max)
>     | (Left   _) = replace {P = \rec => Elem (snd rec) (a' :: (a'' :: as))}
>                            (sym itsEqual)
>                            (There (maxElemLemma tp (a'' :: as) (ltZS m)))
>     | (Right  _) = Here


> {-

> |||
> maxLemma : {A : Type} -> {TO : A -> A -> Type} -> Preordered A TO =>
>            (a : A) -> (as : Vect (S n) A) -> a `Elem` as ->
>            TO a (max as)
> maxLemma {TO} {n = Z}   a (a :: Nil)          Here       = reflexive a
> maxLemma {TO} {n = Z}   a (a' :: Nil)        (There prf) = absurd prf
> maxLemma {TO} {n = S m} a (a :: (a'' :: as))  Here with (preorder a (max (a'' :: as)))
>   | (Left  p) = p
>   | (Right _) = reflexive a
> maxLemma {TO} {n = S m} a (a' :: (a'' :: as)) (There prf) with (preorder a' (max (a'' :: as)))
>   | (Left  _) = maxLemma a (a'' :: as) prf
>   | (Right p) = s3 where
>     s1 : TO a (max (a'' :: as))
>     s1 = maxLemma a (a'' :: as) prf
>     s2 : TO (max (a'' :: as)) a'
>     s2 = p
>     s3 : TO a a'
>     s3 = transitive a (max (a'' :: as)) a' s1 s2


> |||
> argmaxLemma : {A : Type} -> {TO : A -> A -> Type} -> Preordered A TO =>
>               (as : Vect (S n) A) ->
>               index (argmax as) as = max as
> argmaxLemma {TO} {n = Z}   (a :: Nil) = Refl
> argmaxLemma {TO} {n = S m} (a :: (a' :: as)) with (preorder a (max (a' :: as)))
>   | (Left   _) = argmaxLemma (a' :: as)
>   | (Right  _) = Refl

> -}


> {-

> |||
> maxLemma : {A, F : Type} -> {TO : F -> F -> Type} -> Ordered F TO =>
>            (af : (A,F)) -> (afs : Vect (S n) (A,F)) -> af `Elem` afs ->
>            TO (snd af) (max afs)
> maxLemma {A} {F} {TO} {n = Z}   af (af :: Nil)   Here       = reflexive (snd af)
> maxLemma {A} {F} {TO} {n = Z}   af (af' :: Nil) (There prf) = absurd prf
> maxLemma {A} {F} {TO} {n = S m} af (af :: (af'' :: afs)) Here with (order (snd af) (snd (argmaxMax (af'' :: afs))))
>   | (Left  p) = p
>   | (Right _) = reflexive (snd af)
> maxLemma {A} {F} {TO} {n = S m} af (af' :: (af'' :: afs)) (There prf) with (order (snd af') (snd (argmaxMax (af'' :: afs))))
>   | (Left  _) = maxLemma {A} {F} {TO} {n = m} af (af'' :: afs) prf
>   | (Right p) = s3 where
>     s1 : TO (snd af) (max (af'' :: afs))
>     s1 = maxLemma {A} {F} {TO} {n = m} af (af'' :: afs) prf
>     s2 : TO (max (af'' :: afs)) (snd af')
>     s2 = p
>     s3 : TO (snd af) (snd af')
>     s3 = transitive (snd af) (VectOperations.max (af'' :: afs)) (snd af') s1 s2

> -}


Decidability
