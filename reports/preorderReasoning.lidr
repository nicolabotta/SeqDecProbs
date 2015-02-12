> import Data.Fin
> import Syntax.PreorderReasoning

> %default total

> instance Uninhabited (LTE (S n) Z) where
>   uninhabited LTEZero impossible
>   uninhabited (LTESucc x) impossible

> depCong2' : {alpha : Type} -> 
>             {P : alpha -> Type} ->
>             {Q : (a : alpha) -> P a -> Type} ->
>             {a1 : alpha} -> 
>             {a2 : alpha} ->
>             {Pa1 : P a1} ->
>             {Pa2 : P a2} -> 
>             (f : (a : alpha) -> (pa : P a) -> Q a pa) -> 
>             (a1 = a2) ->
>             (Pa1 = Pa2) -> 
>             f a1 Pa1 = f a2 Pa2
> depCong2' f Refl Refl = Refl

> finToNatLemma : (k : Fin n) -> LT (finToNat k) n 
> finToNatLemma {n = Z}   k       =  absurd k
> finToNatLemma {n = S m} FZ      =  LTESucc LTEZero 
> finToNatLemma {n = S m} (FS k)  =  LTESucc (finToNatLemma k) 

> toFin : (Sigma Nat (\ n => LT n b)) -> Fin b
> toFin {b = Z}   (_   ** nLT0)        = void (succNotLTEzero nLT0)
> toFin {b = S m} (Z   ** _)           = FZ
> toFin {b = S m} (S n ** LTESucc prf) = FS (toFin (n ** prf))

> toFinLemma0 : (n : Nat) -> (b : Nat) -> (prf : LT n b) -> 
>               finToNat (toFin (n ** prf)) = n
> toFinLemma0   n     Z             prf = absurd prf
> toFinLemma0   Z    (S a) (LTESucc prf) = Refl
> toFinLemma0  (S m) (S a) (LTESucc prf) = 
>   let ih = toFinLemma0 m a prf in rewrite ih in Refl

> toFinLemma1 : (n : Nat) -> (b : Nat) -> (prf : LT n b) -> 
>               finToNat (FS (toFin (n ** prf))) = S n
> toFinLemma1 n b prf = 
>     ( finToNat (FS (toFin (n ** prf))) )
>   ={ Refl }=
>     ( S (finToNat (toFin (n ** prf)))  )
>   ={ cong (toFinLemma0 n b prf) }=
>     ( S n                              )
>   QED

> toFinLemma2 : (n : Nat) -> (b : Nat) -> (prf : LT n b) -> 
>               finToNatLemma (toFin (n ** prf)) = prf
> toFinLemma2   n     Z     prf              = absurd prf
> toFinLemma2   Z    (S b) (LTESucc LTEZero) = Refl
> --{-
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
> ---}
> {-
> toFinLemma2  (S n) (S b) (LTESucc prf) = trans s1 (trans s2 s3) where
>   s1 : finToNatLemma (toFin (S n ** LTESucc prf))
>        =
>        finToNatLemma (FS (toFin (n ** prf)))
>   s1 = Refl
>   s2 : finToNatLemma (FS (toFin (n ** prf)))
>        =
>        LTESucc (finToNatLemma (toFin (n ** prf)))
>   s2 = Refl
>   s3 : LTESucc (finToNatLemma (toFin (n ** prf)))
>        =
>        LTESucc prf
>   s3 = depCong2' {alpha = Nat}
>                  {P = \ n => LT n b}
>                  {Q = \ n, prf => LT (S n) (S b)}
>                  {a1 = finToNat (toFin (n ** prf))}
>                  {a2 = n}
>                  {Pa1 = finToNatLemma (toFin (n ** prf))}
>                  {Pa2 = prf}
>                  (\ n, prf => LTESucc prf)
>                  (toFinLemma0 n b prf)
>                  (toFinLemma2 n b prf)
> -}

