> module PatterMatchImplicit1
> import Control.Isomorphism
> import Data.Fin

> %default total

> ||| Notion of finiteness for types
> Finite : Type -> Type
> Finite A = Exists (\ n => Iso A (Fin n))

> ||| Mapping |()|s to |Fin|s
> toFin : () -> Fin (S Z)
> toFin () = FZ


> ||| Mapping |Fin (S Z)|s to |()|s
> fromFin : Fin (S Z) -> ()
> fromFin  FZ = ()
> fromFin (FS k) = absurd k


> ||| |toFin| is the left-inverse of |fromFin|
> toFinFromFinLemma : (k : Fin (S Z)) -> toFin (fromFin k) = k
> toFinFromFinLemma FZ = Refl
> toFinFromFinLemma (FS k) = absurd k


> ||| |fromFin| is the left-inverse of |toFin|
> fromFinToFinLemma : (e : ()) -> fromFin (toFin e) = e
> fromFinToFinLemma () = Refl

> ||| Singleton is finite
> finiteSingleton : Finite ()
> finiteSingleton = Evidence (S Z) iso where
>   iso : Iso () (Fin (S Z))
>   iso = MkIso toFin fromFin toFinFromFinLemma fromFinToFinLemma

-----

> X       : (t : Nat) -> Type

> Y       : (t : Nat) -> (x : X t) -> Type

> M : Type -> Type

> step    : (t : Nat) -> (x : X t) -> (y : Y t x) -> M (X (S t))

> Elem     :  {A : Type} -> A -> M A -> Type

> Pred : X t -> X (S t) -> Type
> Pred {t} x x'  =  Exists (\ y => x' `Elem` step t x y)

> Reachable : X t' -> Type
> Reachable {t' =   Z} _   =  ()
> Reachable {t' = S t} x'  =  Exists (\ x => (Reachable x, x `Pred` x'))

> Reachable' : (t' : Nat) -> X t' -> Type
> Reachable' t x = Reachable x



> ||| Works
> finReachable' : {t' : Nat} -> (x : X t') -> Finite (Reachable' t' x)
> finReachable' {t' = Z}   x' = finiteSingleton
> finReachable' {t' = S n} x' = ?foo -- finiteExistsLemma (fX n) (\x => finitePair (finReachable x) (finPred x x'))

> ||| Fails with "Can't unify () with ()"
> finReachable : (x : X t') -> Finite (Reachable x)
> finReachable {t' = Z}   x' = s3 where
>   s1 : (Reachable x') = Unit -- () did not work, but Unit works
>   s1 = Refl
>   s2 : Finite ()
>   s2 = finiteSingleton
>   s3 : Finite (Reachable x')
>   s3 = replace (sym s1) s2

> finReachable {t' = S n} x' = ?foo -- finiteExistsLemma (fX n) (\x => finitePair (finReachable x) (finPred x x'))



-- Local Variables:
-- idris-packages: ("effects")
-- End:
