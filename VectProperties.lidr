> module VectProperties


> import Data.Vect
> import Data.Vect.Quantifiers
> import Data.Fin
> import Syntax.PreorderReasoning
> import Decidable.Order

> import Prop
> import VectOperations
> import Decidable
> import Order


> %default total


> instance Uninhabited (Elem {a} x Nil) where
>   uninhabited Here impossible                                                                                          
>   uninhabited (There p) impossible      


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

> %assert_total
> lookupIndexLemma : (k : Fin n) ->
>                    (xs : Vect n t) ->
>                    (prf : Elem (index k xs) xs) ->
>                    lookup (index k xs) xs prf = k
> lookupIndexLemma  k      Nil       prf        = absurd prf
> lookupIndexLemma  FZ    (x :: xs)  Here       = Refl
> lookupIndexLemma (FS k) (x :: xs) (There prf) = 
>   let ih = lookupIndexLemma k xs prf in rewrite ih in Refl


Membership, quantifiers:

> AnyExistsLemma : {A : Type} -> {P : A -> Prop} -> Any P as -> Exists P
> AnyExistsLemma (Here {x} px) = Evidence x px 
> AnyExistsLemma (There prf) = AnyExistsLemma prf

> ElemAnyLemma : {A : Type} -> {P : A -> Prop} -> P a -> Elem a as -> Any P as
> ElemAnyLemma p Here = Here p
> ElemAnyLemma p (There e) = There (ElemAnyLemma p e)

> decAny : {A : Type} -> {P : A -> Prop} -> Dec1 P -> Dec1 (Any P)
> decAny d1P = any d1P


Filtering

> ||| |filter| preserves membership
> filterLemma : {A : Type} ->
>              {P : A -> Type} ->
>              (d1P : Dec1 P) ->
>              (a : A) ->
>              (as : Vect n A) ->
>              Elem a as ->
>              (p : P a) ->
>              Elem a (getProof (filter d1P as))
> filterLemma d1P a   Nil       prf  p = absurd prf
> filterLemma d1P a1 (a1 :: as) Here p with (filter d1P as)
>   | (n ** as') with (d1P a1)
>     | (Yes _) = Here {x = a1} {xs = as'}
>     | (No  contra) = void (contra p)
> filterLemma d1P a1 (a2 :: as) (There prf) p with (filter d1P as)
>   | (n ** as') with (d1P a2)
>     | (Yes _) = ?issue1920.0 -- There {x = a1} {xs = as'} {y = a2} (filterLemma d1P a1 as prf p)
>     | (No  _) = ?issue1920.1 -- filterLemma {A} {P} d1P a1 as prf p


> ||| |filterTag| preserves membership
> filterTagLemma : {A : Type} ->
>                  {P : A -> Type} ->
>                  (d1P : Dec1 P) ->
>                  (a : A) ->
>                  (as : Vect n A) ->
>                  Elem a as ->
>                  (p : P a) ->
>                  Elem a (map Sigma.getWitness (getProof (filterTag d1P as)))
> filterTagLemma d1P a   Nil       prf  p = absurd prf
> filterTagLemma d1P a1 (a1 :: as) Here p with (filterTag d1P as)
>   | (n ** aps') with (d1P a1)
>     | (Yes _) = Here {x = a1} {xs = map Sigma.getWitness aps'}
>     | (No  contra) = void (contra p)
> filterTagLemma d1P a1 (a2 :: as) (There prf) p with (filterTag d1P as)
>   | (n ** aps') with (d1P a2)
>     | (Yes _) = ?issue1920.2 -- There {x = a1} {xs = map Sigma.getWitness aps'} {y = a2} (filterTagLemma d1P a1 as prf p) 
>     | (No  _) = ?issue1920.3 -- filterTagLemma d1P a1 as prf p


Max and argmax

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

