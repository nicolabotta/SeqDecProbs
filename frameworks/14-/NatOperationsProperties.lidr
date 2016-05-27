> module NatOperationsProperties

> import Syntax.PreorderReasoning

> -- import NatPredicates
> import NatOperations
> import NatBasicProperties
> import NatLTEProperties
> import NatLTProperties
> import Basics


> %default total
> %access public export
> %auto_implicits on


Properties of |pred|:

> |||
> predLemma : (n : Nat) -> (prf : Z `LT` n) -> S (pred n prf) = n
> predLemma  Z    prf = absurd prf
> predLemma (S m) _   = Refl


Properties of |=|:

> ||| EQ is contained in LTE
> eqInLTE : (m : Nat) -> (n : Nat) -> m = n -> m `LTE` n
> eqInLTE  Z     n    prf = LTEZero
> eqInLTE (S m)  Z    prf = absurd prf
> eqInLTE (S m) (S n) prf = LTESucc (eqInLTE m n (succInjective m n prf))
> %freeze eqInLTE


Properties of |plus|:

> |||
> plusPlusElimLeft : {m1, n1, m2, n2 : Nat} -> m1 + n1 = m2 + n2 -> m1 = m2 -> n1 = n2
> plusPlusElimLeft {m1 = Z} {n1} {m2 = Z} {n2} p1 Refl = s2 where
>   s1 : n1 = Z + n2
>   s1 = replace {x = Z + n1}
>                {y = n1}
>                {P = \ ZUZU => ZUZU = Z + n2}
>                (plusZeroLeftNeutral n1)
>                p1
>   s2 : n1 = n2
>   s2 = replace {x = Z + n2}
>                {y = n2}
>                {P = \ ZUZU => n1 = ZUZU}
>                (plusZeroLeftNeutral n2)
>                s1
> plusPlusElimLeft {m1 = Z}    {n1} {m2 = S m2} {n2} p1 Refl impossible
> plusPlusElimLeft {m1 = S m1} {n1} {m2 = Z}    {n2} p1 Refl impossible
> plusPlusElimLeft {m1 = S m1} {n1} {m2 = S m2} {n2} p1 p2 = plusPlusElimLeft p1' p2' where
>   p1' : m1 + n1 = m2 + n2
>   p1' = succInjective (m1 + n1) (m2 + n2) p1
>   p2' : m1 = m2
>   p2' = succInjective m1 m2 p2
> %freeze plusPlusElimLeft

> |||
> plusElimLeft : (m1 : Nat) -> (n : Nat) -> (m2 : Nat) -> m1 + n = m2 -> m1 = m2 -> n = Z
> plusElimLeft m n m p Refl = plusLeftLeftRightZero m n p
> %freeze plusElimLeft

> {-

> |||
> idPlusAnyPreservesLT : (m : Nat) -> (n : Nat) -> m `LT` n -> (p : Nat) -> m `LT` (n + p)

> |||
> idAnyPlusPreservesLT : (m : Nat) -> (n : Nat) -> m `LT` n -> (p : Nat) -> m `LT` (p + n)

> |||
> plusPreservesLT : (m : Nat) -> (n : Nat) -> m `LT` n ->
>                   (p : Nat) -> (q : Nat) -> p `LT` q ->
>                   (m + p) `LT` (n + q)
> plusPreservesLT  Z     Z     zLTz  _ _ _    = absurd  zLTz 
> plusPreservesLT  Z    (S n)  zLTsn p q pLTq = idAnyPlusPreservesLT p q pLTq (S n)
> plusPreservesLT (S m)  Z    smLTz  _ _ _    = absurd smLTz 
> plusPreservesLT (S m) (S n) smLTsn p q pLTq = LTESucc (plusPreservesLT m n (fromLteSucc smLTsn) p q pLTq)

> -}


Properties of |minus|:

> ||| The difference of equal numbers is zero
> minusLemma0 : m = n -> m - n = Z
> minusLemma0 {m = Z}    {n = Z}    Refl = Refl
> minusLemma0 {m = Z}    {n = S n'} prf  = absurd prf
> minusLemma0 {m = S m'} {n = Z}    prf  = absurd prf
> minusLemma0 {m = S m'} {n = S n'} prf  = trans s1 s2 where
>   s1 : S m' - S n' = m' - n'
>   s1 = Refl
>   s2 : m' - n' = Z
>   s2 = minusLemma0 (succInjective m' n' prf)
> %freeze minusLemma0

> |||
> minusLemma1 : n - m = S l -> l = n - (S m)
> minusLemma1 {l} {m = Z}    {n = Z}    p = absurd p
> minusLemma1 {l} {m = Z}    {n = S n'} p = s5 where
>   s1 : S n' = S l
>   s1 = p
>   s2 : l = n'
>   s2 = sym (succInjective n' l s1)
>   s3 : n' = n' - Z
>   s3 = sym (minusZeroRight n')
>   s4 : n' - Z = S n' - S Z
>   s4 = Refl
>   s5 : l = S n' - S Z
>   s5 = trans s2 (trans s3 s4)
> minusLemma1 {l} {m = S m'} {n = Z}    p = absurd p
> minusLemma1 {l} {m = S m'} {n = S n'} p = s3 where
>   s1 : n' - m' = S l
>   s1 = p
>   s2 : l = n' - (S m')
>   s2 = minusLemma1 s1
>   s3 : l = S n' - S (S m')
>   s3 = trans s2 Refl
> %freeze minusLemma1

> |||
> minusLemma2 : LTE m n -> n - m = S l -> LTE (S m) n
> minusLemma2 {m = Z}    {n = Z}    p q = absurd q
> minusLemma2 {m = Z}    {n = S n'} p q = LTESucc LTEZero
> minusLemma2 {m = S m'} {n = Z}    p q = absurd p
> minusLemma2 {m = S m'} {n = S n'} (LTESucc p') q = LTESucc (minusLemma2 p' q)
> %freeze minusLemma2

> |||
> minusLemma3 : LTE m n -> Z = n - m -> m = n
> minusLemma3 {m = Z}    {n = Z}    p q = Refl
> minusLemma3 {m = Z}    {n = S n'} p q = absurd q
> minusLemma3 {m = S m'} {n = Z}    p q = absurd p
> minusLemma3 {m = S m'} {n = S n'} (LTESucc p') q =
>   eqSucc m' n' (minusLemma3 {m = m'} {n = n'} p' q') where
>     q' : Z = n' - m'
>     q' = trans q Refl
> %freeze minusLemma3

> |||
> minusLemma4 : LTE (S m) n -> S (n - S m) = n - m
> minusLemma4 {m = Z} {n = Z}    p = absurd p
> minusLemma4 {m = Z} {n = S n'} (LTESucc p') =
>     ( S (S n' - S Z) )
>   ={ Refl }=
>     ( S (n' - Z)     )
>   ={ cong (minusZeroRight n') }=
>     ( S n'           )
>   ={ Refl }=
>     ( S n' - Z       )
>   QED
> minusLemma4 {m = S m'} {n = Z} p = absurd p
> minusLemma4 {m = S m'} {n = S n'} (LTESucc p') =
>     ( S (S n' - S (S m')) )
>   ={ Refl }=
>     ( S (n' - S m')       )
>   ={ minusLemma4 p' }=
>     ( n' - m'             )
>   ={ Refl }=
>     ( S n' - S m'         )
>   QED
> %freeze minusLemma4


Properties of |plus| and |minus|:

> |||
> plusZeroLeftZero : (m : Nat) -> (n : Nat) -> m + n = Z -> m = Z
> plusZeroLeftZero  Z     Z    _   = Refl
> plusZeroLeftZero  Z    (S n) prf = absurd prf
> plusZeroLeftZero (S m)  Z    prf = absurd prf
> plusZeroLeftZero (S m) (S n) prf = absurd prf
> %freeze plusZeroLeftZero

> |||
> plusZeroRightZero : (m : Nat) -> (n : Nat) -> m + n = Z -> n = Z
> plusZeroRightZero  Z     Z    _   = Refl
> plusZeroRightZero  Z    (S n) prf = absurd prf
> plusZeroRightZero (S m)  Z    prf = absurd prf
> plusZeroRightZero (S m) (S n) prf = absurd prf
> %freeze plusZeroRightZero

> -- plusOneEither : (m : Nat) -> (n : Nat) -> m + n = S Z -> Either (m = Z) (n = Z)

> plusRightInverseMinus : (m : Nat) -> (n : Nat) -> m `LTE` n -> (n - m) + m = n
> plusRightInverseMinus  Z    n _ =
>     ( (n - Z) + Z )
>   ={ plusZeroRightNeutral (n - Z) }=
>     ( n - Z )
>   ={ minusZeroRight n }=
>     ( n )
>   QED
> plusRightInverseMinus (S m) n p =
>     ( (n - S m) + S m )
>   ={ plusCommutative (n - S m) (S m) }=
>     ( S m + (n - S m) )
>   ={ plusSuccRightSucc m (n - S m) }=
>     ( m + S (n - S m) )
>   ={ replace {x = S (n - S m)}
>              {y = n - m}
>              {P = \ ZUZU => m + S (n - S m) = m + ZUZU }
>              (minusLemma4 p) Refl}=
>     ( m + (n - m) )
>   ={ plusCommutative m (n - m) }=
>     ( (n - m) + m )
>   ={ plusRightInverseMinus m n (lteLemma1 m n p) }=
>     ( n )
>   QED
> %freeze plusRightInverseMinus


Properties of |mult|:

> ||| Multiplication of successors is not zero
> multSuccNotZero : (m : Nat) -> (n : Nat) -> Not ((S m) * (S n) = Z)
> multSuccNotZero m  n  p = absurd p
> %freeze multSuccNotZero

> ||| Multiplication of non-zeros is not zero
> multNotZeroNotZero : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Not (n = Z) -> Not (m * n = Z)
> multNotZeroNotZero  Z     n    p q = void (p Refl)
> multNotZeroNotZero (S m)  Z    p q = void (q Refl)
> multNotZeroNotZero (S m) (S n) p q = multSuccNotZero m n
> %freeze multNotZeroNotZero

> ||| Multiplication not zero implies non-zero left
> multNotZeroNotZeroLeft : (m : Nat) -> (n : Nat) -> Not (m * n = Z) -> Not (m = Z)
> multNotZeroNotZeroLeft  Z     n    p = void (p (multZeroLeftZero n))
> multNotZeroNotZeroLeft (S m)  _    _ = SIsNotZ
> %freeze multNotZeroNotZeroLeft

> ||| Multiplication not zero implies non-zero right
> multNotZeroNotZeroRight : (m : Nat) -> (n : Nat) -> Not (m * n = Z) -> Not (n = Z)
> multNotZeroNotZeroRight m  Z     p = void (p (multZeroRightZero m))
> multNotZeroNotZeroRight _ (S n)  _ = SIsNotZ
> %freeze multNotZeroNotZeroRight

> ||| Multiplication of greater-than-zeros is greater than zero
> multZeroLTZeroLT : (m : Nat) -> (n : Nat) -> Z `LT` m -> Z `LT` n -> Z `LT` (m * n)
> multZeroLTZeroLT  Z     n    p _ = absurd p
> multZeroLTZeroLT (S m)  Z    _ q = absurd q
> multZeroLTZeroLT (S m) (S n) _ _ = ltZS (n + m * (S n))
> %freeze multZeroLTZeroLT

> ||| Multiplication greater than zero implies greater than zero left
> multLTZeroLeftLTZero : (m : Nat) -> (n : Nat) -> Z `LT` (m * n) -> Z `LT` m
> multLTZeroLeftLTZero Z n p = absurd p' where
>   p' : Z `LT` Z
>   p' = replace {x = Z * n}
>                {y = Z}
>                {P = \ ZUZU => Z `LT` ZUZU}
>                (multZeroLeftZero n) p
> multLTZeroLeftLTZero (S m) n _ = ltZS m
> %freeze multLTZeroLeftLTZero

> ||| Multiplication greater than zero implies greater than zero right
> multLTZeroRightLTZero : (m : Nat) -> (n : Nat) -> Z `LT` (m * n) -> Z `LT` n
> multLTZeroRightLTZero m Z p = absurd p' where
>   p' : Z `LT` Z
>   p' = replace {x = m * Z}
>                {y = Z}
>                {P = \ ZUZU => Z `LT` ZUZU}
>                (multZeroRightZero m) p
> multLTZeroRightLTZero m (S n) _ = ltZS n
> %freeze multLTZeroRightLTZero

> ||| 
> multZeroRightOneLeftZero : (m : Nat) -> (n : Nat) -> m * (S n) = Z -> m = Z
> multZeroRightOneLeftZero m n prf = plusZeroLeftZero m (n * m) prf' where
>   prf' : (S n) * m = Z
>   prf' = replace {x = m * (S n)} {y = (S n) * m} {P = \ ZUZU => ZUZU = Z} (multCommutative m (S n)) prf
> %freeze multZeroRightOneLeftZero

> |||
> multZeroLeftOneRightZero : (m : Nat) -> (n : Nat) -> (S m) * n = Z -> n = Z
> multZeroLeftOneRightZero m n prf = plusZeroLeftZero n (m * n) prf
> %freeze multZeroLeftOneRightZero

> |||
> multOneLeftOne : (m : Nat) -> (n : Nat) -> m * n = S Z -> m = S Z
> multOneLeftOne  Z     n    prf = absurd prf
> multOneLeftOne (S m)  Z    prf = absurd prf' where
>   prf' : Z = S Z
>   prf' = replace {x = (S m) * Z}
>                  {y = Z}
>                  {P = \ ZUZU => ZUZU = S Z}
>                  (multZeroRightZero (S m)) prf
> multOneLeftOne (S m) (S n) prf = eqSucc m Z s5 where
>   s1 : S (n + m * (S n)) = S Z
>   s1 = prf
>   s2 : n + m * (S n) = Z
>   s2 = succInjective (n + m * (S n)) Z s1
>   s3 : n = Z
>   s3 = plusZeroLeftZero n (m * (S n)) s2
>   s4 : m * (S n) = Z
>   s4 = plusZeroRightZero n (m * (S n)) s2
>   s5 : m = Z
>   s5 = multZeroRightOneLeftZero m n s4
> %freeze multOneLeftOne

> |||
> multOneRightOne : (m : Nat) -> (n : Nat) -> m * n = S Z -> n = S Z
> multOneRightOne m n prf = multOneLeftOne n m prf' where
>   prf' : n * m = S Z
>   prf' = replace {x = m * n} {y = n * m} {P = \ ZUZU => ZUZU = S Z} (multCommutative m n) prf
> %freeze multOneRightOne

> |||
> multPreservesEq : (m1 : Nat) -> (m2 : Nat) -> (n1 : Nat) -> (n2 : Nat) ->
>                   m1 = m2 -> n1 = n2 -> m1 * n1 = m2 * n2
> multPreservesEq m m n n Refl Refl = Refl
> %freeze multPreservesEq

> |||
> multMultElimLeft : (m1 : Nat) -> (m2 : Nat) -> (n1 : Nat) -> (n2 : Nat) ->
>                    m1 = m2 -> Not (m1 = Z) -> m1 * n1 = m2 * n2 -> 
>                    n1 = n2
> multMultElimLeft _  _   Z      Z     _      _      _            = Refl
> multMultElimLeft m1 m2  Z     (S n2) m1EQm2 nm1EQZ m1ZEQm2sn2   = 
>   void (nm1EQZ s4) where
>     s0  :  m1 * Z = m2 * (S n2)
>     s0  =  m1ZEQm2sn2
>     s1  :  Z = m2 * (S n2)
>     s1  =  replace {x = m1 * Z} {y = Z} {P = \ ZUZU => ZUZU = m2 * (S n2)} (multZeroRightZero m1) s0
>     s2  :  Z = m2
>     s2  =  sym (multZeroRightOneLeftZero m2 n2 (sym s1))
>     s3  :  m2 = Z
>     s3  =  sym s2
>     s4  :  m1 = Z
>     s4  =  replace (sym m1EQm2) s3
> multMultElimLeft m1 m2 (S n1)  Z     m1EQm2 nm1EQZ m1sn1EQm2Z   = 
>   void (nm1EQZ s2) where
>     s0  :  m1 * (S n1) = m2 * Z
>     s0  =  m1sn1EQm2Z
>     s1  :  m1 * (S n1) = Z
>     s1  =  replace {x = m2 * Z} {y = Z} {P = \ ZUZU => m1 * (S n1) = ZUZU} (multZeroRightZero m2) s0
>     s2  :  m1 = Z
>     s2  =  multZeroRightOneLeftZero m1 n1 s1
> multMultElimLeft m1 m2 (S n1) (S n2) m1EQm2 nm1EQZ m1sn1EQm2sn2 = 
>   eqSucc n1 n2 s5 where
>     s0  :  m1 * (S n1) = m2 * (S n2)
>     s0  =  m1sn1EQm2sn2
>     s1  :  (S n1) * m1 = (S n2) * m2
>     s1  =  replace2 {a = Nat} {a1 = m1 * (S n1)} {a2 = (S n1) * m1} 
>                     {b = Nat} {b1 = m2 * (S n2)} {b2 = (S n2) * m2} 
>                     {P = \ ZUZU => \ ZAZA => ZUZU = ZAZA}
>                     (multCommutative m1 (S n1)) (multCommutative m2 (S n2)) s0
>     s2  :  m1 + n1 * m1 = m2 + n2 * m2
>     s2  =  s1
>     s3  :  n1 * m1 = n2 * m2
>     s3  =  plusPlusElimLeft s2 m1EQm2
>     s4  :  m1 * n1 = m2 * n2
>     s4  =  replace2 {a = Nat} {a1 = n1 * m1} {a2 = m1 * n1}
>                     {b = Nat} {b1 = n2 * m2} {b2 = m2 * n2}
>                     {P = \ ZUZU => \ ZAZA => ZUZU = ZAZA}
>                     (multCommutative n1 m1) (multCommutative n2 m2) s3
>     s5  :  n1 = n2
>     s5  =  multMultElimLeft m1 m2 n1 n2 m1EQm2 nm1EQZ s4

> |||
> multMultElimRight : (m1 : Nat) -> (m2 : Nat) -> (n1 : Nat) -> (n2 : Nat) ->
>                     n1 = n2 -> Not (n1 = Z) -> m1 * n1 = m2 * n2 -> 
>                     m1 = m2
> multMultElimRight m1 m2 n1 n2 n1EQn2 nn1EQZ prf =
>   multMultElimLeft n1 n2 m1 m2 n1EQn2 nn1EQZ prf' where
>     prf' : n1 * m1 = n2 * m2
>     prf' = replace2 (multCommutative m1 n1) (multCommutative m2 n2) prf

> |||
> multElim1 : (m : Nat) -> (n : Nat) -> (S m) * n = S m -> n = S Z
> multElim1 m    Z  p = absurd s1 where
>   s1 : Z = S m
>   s1 = replace {x = (S m) * Z} {y = Z} {P = \ ZUZU => ZUZU = S m} (multZeroRightZero (S m)) p
> multElim1 m (S Z) _ = Refl
> multElim1 m (S (S n)) p = void (multSuccNotZero n m s5) where
>   s1 : (S (S n)) * (S m) = S m
>   s1 = replace {x = (S m) * (S (S n))}
>                {y = (S (S n)) * (S m)}
>                {P = \ ZUZU => ZUZU = S m}
>                (multCommutative (S m) (S (S n))) p
>   s2 : S m + (S n) * (S m) = S m
>   s2 = replace {x = (S (S n)) * (S m)}
>                {y = S m + (S n) * (S m)}
>                {P = \ ZUZU => ZUZU = S m}
>                Refl s1
>   s5 : (S n) * (S m) = Z
>   s5 = plusLeftLeftRightZero (S m) ((S n) * (S m)) s2
> %freeze multElim1

> |||
> multSwapLeft : (a, b, c : Nat) -> a * b * c = b * a * c
> multSwapLeft a b c = ( a * b * c )
>                    ={ Refl }=
>                      ( (a * b) * c )
>                    ={ cong {f = \ ZUZU => ZUZU * c} (multCommutative a b) }=
>                      ( (b * a) * c )
>                    ={ Refl }=
>                      ( b * a * c )
>                    QED
> %freeze multSwapLeft

> |||
> multSwapRight : (a, b, c : Nat) -> a * b * c = a * c * b
> multSwapRight a b c = ( a * b * c )
>                     ={ Refl }=
>                       ( (a * b) * c )
>                     ={ sym (multAssociative a b c) }=
>                       ( a * (b * c) )
>                     ={ cong (multCommutative b c) }=
>                       ( a * (c * b) )
>                     ={ multAssociative a c b }=
>                       ( (a * c) * b )
>                     ={ Refl }=
>                       ( a * c * b )
>                     QED
> %freeze multSwapRight

> |||
> multSwap23 : (a, b, c, d : Nat) -> (a * b) * (c * d) = (a * c) * (b * d)
> multSwap23 a b c d = ( (a * b) * (c * d) )
>                    ={ Refl }=
>                      ( a * b * (c * d) )
>                    ={ sym (multAssociative a b (c * d)) }=
>                      ( a * (b * (c * d)) )
>                    ={ cong {f = \ ZUZU => a * ZUZU} (multAssociative b c d) }=
>                      ( a * ((b * c) * d) )
>                    ={ cong {f = \ ZUZU => a * ZUZU} (multSwapLeft b c d) }=
>                      ( a * ((c * b) * d) )
>                    ={ cong {f = \ ZUZU => a * ZUZU} (sym (multAssociative c b d)) }=
>                      ( a * (c * (b * d)) )
>                    ={ multAssociative a c (b * d) }=
>                      ( a * c * (b * d) )
>                    ={ Refl }=
>                      ( (a * c) * (b * d) )
>                    QED

> |||
> multSwap24 : (a, b, c, d : Nat) -> (a * b) * (c * d) = (a * d) * (c * b)
> multSwap24 a b c d = ( (a * b) * (c * d) )
>                    ={ cong {f = \ ZUZU => (a * b) * ZUZU} (multCommutative c d) }=
>                      ( (a * b) * (d * c) )
>                    ={ multSwap23 a b d c }=
>                      ( (a * d) * (b * c) )
>                    ={ cong {f = \ ZUZU => (a * d) * ZUZU} (multCommutative b c) }=
>                      ( (a * d) * (c * b) )
>                    QED

> |||
> multFlipCentre : (m1 : Nat) -> (m2 : Nat) -> (n1 : Nat) -> (n2 : Nat) ->
>                  (m1 * m2) * (n1 * n2) = (m1 * n1) * (m2 * n2)
> multFlipCentre = multSwap23
> %freeze multFlipCentre

> |||
> multOneRightNeutralPlusMultZeroLeftZero : (m : Nat) -> (n : Nat) -> m * 1 + 0 * n = m
> multOneRightNeutralPlusMultZeroLeftZero m n =
>     ( m * 1 + 0 * n )
>   ={ cong (multZeroLeftZero n) }=
>     ( m * 1 + 0 )
>   ={ cong {f = \ ZUZU => ZUZU + 0} (multOneRightNeutral m) }=
>     ( m + 0 )
>   ={ plusZeroRightNeutral m }=  
>     ( m )
>   QED
> %freeze multOneRightNeutralPlusMultZeroLeftZero


Properties of |sum|:

> ||| |sum| is monotone
> sumMon : {A : Type} ->
>          (f : A -> Nat) -> (g : A -> Nat) ->
>          (p : (a : A) -> f a `LTE` g a) ->
>          (as : List A) ->
>          sum (map f as) `LTE` sum (map g as) 
> sumMon f g p Nil = LTEZero
> sumMon f g p (a :: as) = s5 where
>   s1 : sum (map f (a :: as)) = f a + sum (map f as)
>   s1 = Refl
>   s2 : sum (map g (a :: as)) = g a + sum (map g as)
>   s2 = Refl
>   s3 : f a `LTE` g a
>   s3 = p a
>   s4 : sum (map f as) `LTE` sum (map g as)
>   s4 = sumMon f g p as
>   s5 : sum (map f (a :: as)) `LTE` sum (map g (a :: as))
>   s5 = monotoneNatPlusLTE s3 s4


> {-
> ||| |min| is monotone
> postulate minMon : {A : Type} ->
>                    (f : A -> Nat) -> (g : A -> Nat) ->
>                    (p : (a : A) -> f a `LTE` g a) ->
>                    (as : List A) ->
>                    min (map f as) `LTE` min (map g as) 
> -}


> {-

Test:

> CLTtoLT : {m, n : Nat} -> compare m n = LT -> m `LT` n

> LTtoCLT : {m, n : Nat} -> m `LT` n -> compare m n = LT

> CEQtoEQ : {m, n : Nat} -> compare m n = EQ -> m = n

> EQtoCEQ : {m, n : Nat} -> m = n -> compare m n = EQ


> anyPlusPreservesOrd : {x, y, z : Nat} -> {ORD : Ordering} -> 
>                       compare x y = ORD -> compare (z + x) (z + y) = ORD

> plusAnyPreservesOrd : {x, y, z : Nat} -> {ORD : Ordering} -> 
>                       compare x y = ORD -> compare (z + x) (z + y) = ORD

> LTinLTE : {m, n : Nat} -> LT m n -> LTE m n

> pLTpEQpLTE : (LT x1 x2 -> LT y1 y2) -> (x1 = x2 -> y1 = y2) -> (LTE x1 x2 -> LTE y1 y2)

> anyPlusPreservesLT : LT x y -> LT (z + x) (z + y)
> anyPlusPreservesLT {x} {y} {z} prf = s3 where
>   s1  :  compare x y = LT
>   s1  =  LTtoCLT prf
>   s2  :  compare (z + x) (z + y) = LT
>   s2  =  anyPlusPreservesOrd s1
>   s3  :  (z + x) `LT` (z + y) 
>   s3  =  CLTtoLT s2

> anyPlusPreservesEQ : {x, y, z : Nat} -> x = y -> (z + x) = (z + y)
> anyPlusPreservesEQ {x} {y} {z} prf = s3 where
>   s1  :  compare x y = EQ
>   s1  =  EQtoCEQ prf
>   s2  :  compare (z + x) (z + y) = EQ
>   s2  =  anyPlusPreservesOrd s1
>   s3  :  (z + x) = (z + y) 
>   s3  =  CEQtoEQ s2

> anyPlusPreservesLTE : LTE x y -> LTE (z + x) (z + y)
> anyPlusPreservesLTE = pLTpEQpLTE anyPlusPreservesLT anyPlusPreservesEQ

> ---}
