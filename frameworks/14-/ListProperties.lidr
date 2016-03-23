> module ListProperties

> import Data.List
> import Data.List.Quantifiers
> import Data.Fin
> import Control.Isomorphism
> import Syntax.PreorderReasoning

> import FunOperations
> import Unique
> import Finite
> import FiniteOperations
> import Sigma
> import PairsOperations
> import Basics
> import IsomorphismOperations
> import FinProperties


> %default total
> %auto_implicits off
> %access public export


|List| is a functor:

> -- functorSpec1 : fmap . id = id

> -- functorSpec2 : fmap (f . g) = (fmap f) . (fmap g)


|List| is a monad:

> -- monadSpec1 : (fmap f) . ret = ret . f

> -- monadSpec21 : bind (ret a) f = f a

> -- monadSpec22 : bind ma ret = ma

> -- monadSpec23 : {A, B, C : Type} -> {f : A -> M B} -> {g : B -> M C} ->
> --                bind (bind ma f) g = bind ma (\ a => bind (f a) g)


|List| is a container monad:

> -- containerMonadSpec1 : a `Elem` (ret a)

> -- containerMonadSpec2 : {A : Type} -> (a : A) -> (ma : M A) -> (mma : M (M A)) ->
> --                       a `Elem` ma -> ma `Elem` mma -> a `Elem` (join mma)

> containerMonadSpec3 : {A : Type} -> {P : A -> Type} -> (a : A) -> (as : List A) ->
>                       All P as -> a `Elem` as -> P a
> containerMonadSpec3 a'  Nil       _           eprf        = absurd eprf
> containerMonadSpec3 a' (a :: as)  Nil         _           impossible
> containerMonadSpec3 a  (a :: as) (pa :: pas)  Here        = pa
> containerMonadSpec3 a' (a :: as) (pa :: pas) (There eprf) = containerMonadSpec3 a' as pas eprf
> %freeze containerMonadSpec3

> -- containerMonadSpec4 : {A : Type} -> (ma : M A) -> fmap outl (tagElem ma) = ma


Quantifiers properties:

> uniqueAllLemma : {A : Type} -> {P : A -> Type} -> 
>                  Unique1 P -> (as : List A) -> Unique (All P as)
> uniqueAllLemma u1P  Nil      Nil Nil = Refl
> uniqueAllLemma u1P (a :: as) (pa :: pas) (pa' :: pas') = 
>     ( pa :: pas )
>   ={ replace {P = \ ZUZU => pa :: pas = ZUZU :: pas} (u1P a pa pa') Refl }=
>     ( pa' :: pas )
>   ={ replace {P = \ ZUZU => pa' :: pas = pa' :: ZUZU} (uniqueAllLemma u1P as pas pas') Refl }=
>     ( pa' :: pas' ) 
>   QED   


> ||| 
> finiteAllLemma0 : {A : Type} -> {P : A -> Type} -> 
>                   Finite1 P -> Iso (All P Nil) Unit
> finiteAllLemma0 f1P = MkIso to from toFrom fromTo where
>   to : All P Nil -> Unit
>   to Nil = () 
>   from : Unit -> All P Nil
>   from () = Nil
>   toFrom : (k : Unit) -> to (from k) = k
>   toFrom () = Refl
>   fromTo : (nil : All P Nil) -> from (to nil) = nil
>   fromTo Nil = Refl


> |||
> finiteAllLemma1 : {A : Type} -> {P : A -> Type} -> 
>                   Finite1 P -> (a : A) -> (as : List A) -> 
>                   Iso (All P (a :: as)) (P a, All P as)
> finiteAllLemma1 {P} f1P a as = MkIso to from toFrom fromTo where
>   to : All P (a :: as) -> (P a, All P as)
>   to (pa :: pas) = (pa, pas)
>   from : (P a, All P as) -> All P (a :: as)
>   from (pa, pas) = pa :: pas
>   toFrom : (papas : (P a, All P as)) -> to (from papas) = papas
>   toFrom (pa, pas) = Refl
>   fromTo : (papas : All P (a :: as)) -> from (to papas) = papas
>   fromTo (pa :: pas) = Refl


> |||
> finiteAllLemma : {A : Type} -> {P : A -> Type} -> 
>                  Finite1 P -> (as : List A) -> Finite (All P as)
> finiteAllLemma {P} f1P Nil = MkSigma (S Z) iso where
>   iso : Iso (All P Nil) (Fin (S Z))
>   iso = isoTrans (finiteAllLemma0 f1P) (isoSym isoFin1Unit)
> finiteAllLemma {P} f1P (a :: as) = MkSigma n iso where
>   fH : Finite (P a)
>   fH = f1P a
>   mH : Nat
>   mH = getWitness fH
>   isoH : Iso (P a) (Fin mH)
>   isoH = getProof fH
>   fT : Finite (All P as)
>   fT = finiteAllLemma f1P as
>   mT : Nat
>   mT = getWitness fT
>   isoT : Iso (All P as) (Fin mT)
>   isoT = getProof fT
>   n  : Nat
>   n  = mH * mT
>   iso1 : Iso (All P (a :: as)) (P a, All P as)
>   iso1 = finiteAllLemma1 f1P a as
>   iso2 : Iso (P a, All P as) (Fin mH, Fin mT)
>   iso2 = pairCong isoH isoT
>   iso3 : Iso (Fin mH, Fin mT) (Fin (mH * mT))
>   iso3 = finPairTimes
>   iso  : Iso (All P (a :: as)) (Fin n)
>   iso  = isoTrans iso1 (isoTrans iso2 iso3)


Fusion-related properties:

> ||| 
> mapSndMapCrossAnyIdLemma : {A, B, C : Type} -> 
>                            (f : A -> C) -> 
>                            (abs : List (A, B)) -> 
>                            map snd (map (cross f id) abs) = map snd abs
> mapSndMapCrossAnyIdLemma _ Nil = Refl
> mapSndMapCrossAnyIdLemma f ((a, b) :: abs) = 
>     ( map snd (map (cross f id) ((a, b) :: abs)) )
>   ={ Refl }=
>     ( map snd ((f a, b) :: map (cross f id) abs) )
>   ={ Refl }=
>     ( b :: map snd (map (cross f id) abs) )
>   ={ cong (mapSndMapCrossAnyIdLemma f abs) }=
>     ( b :: map snd abs )
>   ={ Refl }=
>     ( map snd ((a, b) :: abs) )
>   QED
> %freeze mapSndMapCrossAnyIdLemma



