> module BoundedNatProperties

> import Data.Fin
> import Control.Isomorphism
> import Syntax.PreorderReasoning

> import BoundedNat
> import BoundedNatOperations
> import Basics
> import NatLTProperties
> import Sigma
> import PairsOperations
> import SigmaProperties
> import FinProperties
> import Finite
> import Unique

> %default total
> %access public export
> %auto_implicits on


No natural number is smaller than zero

> implementation Uninhabited (LTB Z) where
>   uninhabited (MkSigma n prf) = absurd prf


Basic properties

> |||
> toFinLemma0 : (n : Nat) -> (b : Nat) -> (prf : LT n b) ->
>               finToNat (toFin (MkSigma n prf)) = n
> toFinLemma0   n     Z             prf  = absurd prf
> toFinLemma0   Z    (S a) (LTESucc prf) = Refl
> toFinLemma0  (S m) (S a) (LTESucc prf) = let ih = toFinLemma0 m a prf
>                                          in rewrite ih in Refl
> %freeze toFinLemma0 -- frozen


> |||
> toFinLemma1 : (n : Nat) -> (b : Nat) -> (prf : LT n b) ->
>               finToNat (FS (toFin (MkSigma n prf))) = S n
> toFinLemma1 n b prf =
>     ( finToNat (FS (toFin (MkSigma n prf))) )
>   ={ Refl }=                             -- definition of |finToNat|
>     ( S (finToNat (toFin (MkSigma n prf)))  )
>   ={ cong (toFinLemma0 n b prf) }=       -- |toFinLemma0|, functionality of |S|
>     ( S n                              )
>   QED
> %freeze toFinLemma1 -- frozen


> |||
> toFinLemma2 : (n : Nat) -> (b : Nat) -> (prf : LT n b) ->
>               finToNatLemma (toFin (MkSigma n prf)) = prf
> toFinLemma2   n     Z     prf              = absurd prf
> toFinLemma2   Z    (S b) (LTESucc LTEZero) = Refl
> {-
> toFinLemma2  (S n) (S b) (LTESucc prf) =
>     ( finToNatLemma (toFin (S n ** LTESucc prf)) )
>   ={ Refl }=                                       -- definition of |toFin|
>     ( finToNatLemma (FS (toFin (n ** prf)))      )
>   ={ Refl }=                                       -- definition of |finToNatLemma|
>     ( LTESucc (finToNatLemma (toFin (n ** prf))) )
>   ={ depCong2' {alpha = Nat}
>                {P = \ n => LT n b}
>                {Q = \ n, prf => LT (S n) (S b)}
>                {a1 = finToNat (toFin (n ** prf))}
>                {a2 = n}
>                {Pa1 = finToNatLemma (toFin (n ** prf))}
>                {Pa2 = prf}
>                (\ n, prf => LTESucc prf)
>                (toFinLemma0 n b prf)
>                (toFinLemma2 n b prf) }=
>     ( LTESucc prf                                )
>   QED
> -}
> --{-
> toFinLemma2  (S n) (S b) (LTESucc prf) = trans s1 (trans s2 s3) where
>   s1 : finToNatLemma (toFin (MkSigma (S n) (LTESucc prf)))
>        =
>        finToNatLemma (FS (toFin (MkSigma n prf)))
>   s1 = Refl
>   s2 : finToNatLemma (FS (toFin (MkSigma n prf)))
>        =
>        LTESucc (finToNatLemma (toFin (MkSigma n prf)))
>   s2 = Refl
>   {-
>   sx : finToNatLemma (toFin (n ** prf))
>        =
>        prf
>   sx = toFinLemma2 n b prf
>   sy : LTESucc (finToNatLemma (toFin (n ** prf)))
>        =
>        LTESucc prf
>   sy = cong {a = finToNatLemma (toFin (n ** prf))} {b = prf} {f = LTESucc} sx
>   -}
>   s3 : LTESucc (finToNatLemma (toFin (MkSigma n prf)))
>        =
>        LTESucc prf
>   s3 = depCong2' {alpha = Nat}
>                  {P = \ n => LT n b}
>                  {Q = \ n, prf => LT (S n) (S b)}
>                  {a1 = finToNat (toFin (MkSigma n prf))}
>                  {a2 = n}
>                  {Pa1 = finToNatLemma (toFin (MkSigma n prf))}
>                  {Pa2 = prf}
>                  {f = \ n, prf => LTESucc prf}
>                  (toFinLemma0 n b prf)
>                  (toFinLemma2 n b prf)
> ---}
> %freeze toFinLemma2 -- frozen


> |||
> toFinLemma3 : (n : Nat) -> (b : Nat) -> (prf : LT n b) ->
>               finToNatLemma (FS (toFin (MkSigma n prf))) = LTESucc prf
> {-
> toFinLemma3 n b prf =
>     ( finToNatLemma (FS (toFin (n ** prf)))      )
>   ={ replace {a = Fin (S b)}
>              {x = FS (toFin (n ** prf))}
>              {y = toFin (S n ** LTESucc prf)}
>              {P = \ x => finToNatLemma (FS (toFin (n ** prf))) = finToNatLemma x}
>              Refl Refl }=
>     ( finToNatLemma (toFin (S n ** LTESucc prf)) )
>   ={ toFinLemma2 (S n) (S b) (LTESucc prf) }=
>     ( LTESucc prf                                )
> -}
> toFinLemma3 n b prf = trans s1 s2 where
>   s0 : FS (toFin (MkSigma n prf)) = toFin (MkSigma (S n) (LTESucc prf))
>   s0 = Refl
>   s1 : finToNatLemma (FS (toFin (MkSigma n prf)))
>        =
>        finToNatLemma (toFin (MkSigma (S n) (LTESucc prf)))
>   s1 = replace {a = Fin (S b)}
>                {x = FS (toFin (MkSigma n prf))}
>                {y = toFin (MkSigma (S n) (LTESucc prf))}
>                {P = \ x => finToNatLemma (FS (toFin (MkSigma n prf))) = finToNatLemma x}
>                s0 Refl
>   s2 : finToNatLemma (toFin (MkSigma (S n) (LTESucc prf)))
>        =
>        LTESucc prf
>   s2 = toFinLemma2 (S n) (S b) (LTESucc prf)
> %freeze toFinLemma3 -- frozen


> {-
> |||
> toFinLemma6 : (n : Nat) -> (b : Nat) -> (prf : LT n b) ->
>               toFin (S n ** LTESucc prf) = FS (toFin (n ** prf))
> -}


> ||| |toFin| is the left-inverse of |fromFin|
> toFinFromFinLemma : (k : Fin b) -> toFin (fromFin k) = k
> toFinFromFinLemma {b = Z} k = absurd k
> toFinFromFinLemma {b = S m} FZ = Refl
> toFinFromFinLemma {b = S m} (FS k) =
>   let ih = toFinFromFinLemma k in
>   rewrite ih in
>   Refl
> %freeze toFinFromFinLemma -- frozen


> ||| |fromFin| is the left-inverse of |toFin|
> fromFinToFinLemma : (n : LTB b) -> fromFin (toFin n) = n
> fromFinToFinLemma {b = Z}   m                         = absurd m
> fromFinToFinLemma {b = S m} (MkSigma   Z    (LTESucc LTEZero))  = Refl
> fromFinToFinLemma {b = S m} (MkSigma (S n) (LTESucc prf))      = s6 where
>   s1 : fromFin (toFin (MkSigma (S n) (LTESucc prf)))
>        =
>        fromFin (FS (toFin (MkSigma n prf)))
>   s1 = Refl
>   s2 : fromFin (FS (toFin (MkSigma n prf)))
>        =
>        MkSigma (finToNat (FS (toFin (MkSigma n prf)))) (finToNatLemma (FS (toFin (MkSigma n prf))))
>   s2 = Refl
>   s3 : finToNat (FS (toFin (MkSigma n prf))) = S n
>   s3 = toFinLemma1 n m prf
>   s4 : finToNatLemma (FS (toFin (MkSigma n prf))) = LTESucc prf
>   s4 = toFinLemma3 n m prf
>   s5 : MkSigma {a = Nat} {P = \ i => LT i (S m)}
>        (finToNat (FS (toFin (MkSigma n prf))))
>        (finToNatLemma (FS (toFin (MkSigma n prf))))
>        =
>        MkSigma {a = Nat} {P = \ i => LT i (S m)} (S n) (LTESucc prf)
>   s5 = depCong2 {f = MkSigma {a = Nat} {P = \ i => LT i (S m)}} s3 s4
>   s6 : fromFin (toFin (MkSigma (S n) (LTESucc prf))) = MkSigma (S n) (LTESucc prf)
>   s6 = trans s1 (trans s2 s5)
> %freeze fromFinToFinLemma -- frozen


Finitness properties

> ||| Bounded |Nat|s are finite:
> finiteLTB : (b : Nat) -> Finite (LTB b)
> finiteLTB b = MkSigma b iso where
>   iso : Iso (LTB b) (Fin b)
>   iso = MkIso toFin fromFin toFinFromFinLemma fromFinToFinLemma
> %freeze finiteLTB -- frozen


> {-
> ||| Subtypes of bounded |Nat|s are finite:
> finiteSubLTB : (b : Nat) -> (P : LTB b -> Type) -> Dec1 P -> (uP : Unique1 P) -> Finite (SubType (LTB b) P uP)
> finiteSubLTB b P dP uP = finiteSubTypeLemma0 {A = LTB b} {P} (finiteLTB b) dP uP
> -}


Decidability properties

> ||| Equality of bounded |Nat|s is decidable
> decEqLTB : {b : Nat} -> (i : LTB b) -> (j : LTB b) -> Dec (i = j)
> decEqLTB {b} (MkSigma m p) (MkSigma n q) with (decEq m n)
>   | (Yes prf)   = Yes (sigmaEqLemma1 (MkSigma m p) (MkSigma n q) prf (uniqueLT))
>   | (No contra) = No (\ prf => contra (getWitnessPreservesEq prf))
> %freeze decEqLTB -- frozen


> implementation DecEq (LTB b) where
>   decEq {b} i j = decEqLTB {b} i j


Show

> using (b : Nat)
>   implementation Show (LTB b) where
>     show (MkSigma i _) = show i

