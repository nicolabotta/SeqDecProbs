> module NatProperties


> import Decidable.Order
> import Syntax.PreorderReasoning

> import NatPredicates
> import NatOperations
> import Preorder
> import TotalPreorder
> import Basics


> %default total


> instance Uninhabited (S n = Z) where
>   uninhabited Refl impossible


> {-
> instance Uninhabited (LTE (S n) Z) where
>   uninhabited LTEZero impossible
>   uninhabited (LTESucc x) impossible

> lteRefl : LTE n n
> lteRefl {n = Z}   = LTEZero
> lteRefl {n = S k} = LTESucc lteRefl

> -}

> {- Not used

> eitherLemma : (m : Nat) -> (n : Nat) -> Either (m = n) (Either (m `LT` n) (n `LT` m))
> eitherLemma Z  Z    = Left Refl

> -}


EQ properties

> predInjective : (left : Nat) -> (right : Nat) -> Not (S left = S right) -> Not (left = right)
> predInjective left right contra = contra . (eqSucc left right)
> %freeze predInjective

> succInjective' : (left : Nat) -> (right : Nat) -> Not (left = right) -> Not (S left = S right)
> succInjective' left right contra = contra . (succInjective left right)
> %freeze succInjective'


LT, LTE properties

> notLTELemma0 : Not (S m `LTE` S n) -> Not (m `LTE` n)
> notLTELemma0 contra = contra . LTESucc
> %freeze notLTELemma0

> notLTELemma1 : (m : Nat) -> (n : Nat) -> Not (m `LTE` n) -> n `LTE` m
> notLTELemma1  m     Z    p = LTEZero
> notLTELemma1  Z    (S n) p = void (p LTEZero)
> notLTELemma1 (S m) (S n) p = LTESucc (notLTELemma1 m n (notLTELemma0 p))
> %freeze notLTELemma1

> |||
> lteLemma1 : (m : Nat) -> (n : Nat) -> LTE (S m) n -> LTE m n
> lteLemma1  Z     Z             prf  = absurd prf
> lteLemma1  Z    (S n)  LTEZero        impossible
> lteLemma1  Z    (S n) (LTESucc prf) = LTEZero
> lteLemma1 (S m)  Z             prf  = absurd prf
> lteLemma1 (S m) (S n)  LTEZero        impossible
> lteLemma1 (S m) (S n) (LTESucc prf) = LTESucc (lteLemma1 m n prf)
> %freeze lteLemma1

> |||
> ltLemma1 : (m : Nat) -> (n : Nat) -> LT (S m) n -> LT m n
> ltLemma1 m n prf = lteLemma1 (S m) n prf
> %freeze ltLemma1

> ||| LT is contained in LTE
> ltInLTE : (m : Nat) -> (n : Nat) -> LT m n -> LTE m n
> ltInLTE = lteLemma1
> %freeze ltInLTE

> ||| EQ is contained in LTE
> eqInLTE : (m : Nat) -> (n : Nat) -> m = n -> m `LTE` n
> eqInLTE  Z     n    prf = LTEZero
> eqInLTE (S m)  Z    prf = absurd prf
> eqInLTE (S m) (S n) prf = LTESucc (eqInLTE m n (succInjective m n prf))
> %freeze eqInLTE

> |||
> idSuccPreservesLTE : (m : Nat) -> (n : Nat) -> m `LTE` n -> m `LTE` (S n)
> idSuccPreservesLTE  Z     n    prf = LTEZero
> idSuccPreservesLTE (S m)  Z    prf = absurd prf
> idSuccPreservesLTE (S m) (S n) prf = LTESucc (idSuccPreservesLTE m n (fromLteSucc prf))
> %freeze idSuccPreservesLTE

> ||| Zero is smaller than any successor
> ltZS : (m : Nat) -> LT Z (S m)
> ltZS  Z    = LTESucc LTEZero
> ltZS (S m) = idSuccPreservesLTE (S Z) (S m) (ltZS m)
> %freeze ltZS

> ||| Any number is smaller than its successor
> ltIdS : (m : Nat) -> LT m (S m)
> ltIdS  Z    = LTESucc LTEZero
> ltIdS (S m) = LTESucc (ltIdS m)
> %freeze ltIdS

> ||| Any number which is not zero is greater than zero
> notZisgtZ : {n : Nat} -> Not (n = Z) -> LT Z n
> notZisgtZ {n = Z}   contra = void (contra Refl)
> notZisgtZ {n = S m} _      = ltZS m
> %freeze notZisgtZ

> ||| Any number which is greater than zero is not zero
> gtZisnotZ : {n : Nat} -> LT Z n -> Not (n = Z)
> gtZisnotZ {n = Z}   p = absurd p
> gtZisnotZ {n = S m} p = absurd
> %freeze gtZisnotZ

> ||| No number is less than zero
> notLTzero : {n : Nat} -> Not (LT n Z)
> notLTzero = succNotLTEzero
> %freeze notLTzero

> |||
> strengthenLT : (m : Nat) -> (n : Nat) -> LT m (S n) -> Not (m = n) -> LT m n
> strengthenLT  Z       n  _       zNEQn   = notZisgtZ (zNEQn . sym)
> strengthenLT (S m)  Z    smLTsz  _       = void (notLTzero (fromLteSucc smLTsz))
> strengthenLT (S m) (S n) smLTssn smNEQsn = LTESucc mLTn where
>   mLTsn : LT m (S n)
>   mLTsn = fromLteSucc smLTssn
>   mNEQn : Not (m = n)
>   mNEQn = predInjective m n smNEQsn
>   mLTn : LT m n
>   mLTn = strengthenLT m n mLTsn mNEQn
> %freeze strengthenLT

> monotoneNatPlusLTE : {x : Nat} -> {y : Nat} ->
>                      (z : Nat) -> LTE x y -> LTE (z + x) (z + y)
> monotoneNatPlusLTE {x} {y}  Z    xLTEy = xLTEy
> monotoneNatPlusLTE {x} {y} (S n) xLTEy = LTESucc (monotoneNatPlusLTE {x} {y} n xLTEy)
> --%freeze monotoneNatPlusLTE

> reflexiveLTE : (n : Nat) -> LTE n n
> reflexiveLTE n = lteRefl {n}
> --%freeze reflexiveLTE

> transitiveLTE : (m : Nat) -> (n : Nat) -> (o : Nat) ->
>                 LTE m n -> LTE n o -> LTE m o
> transitiveLTE  Z       n     o   LTEZero                 nlteo  = LTEZero
> transitiveLTE (S m) (S n) (S o) (LTESucc mlten) (LTESucc nlteo) = LTESucc (transitiveLTE m n o mlten nlteo)
> --%freeze transitiveLTE

> totalLTE : (m : Nat) -> (n : Nat) -> Either (LTE m n) (LTE n m)
> totalLTE  Z    n     = Left LTEZero
> totalLTE (S m) Z     = Right LTEZero
> totalLTE (S m) (S n) with (totalLTE m n)
>   | (Left  p) = Left  (LTESucc p)
>   | (Right p) = Right (LTESucc p)
> --%freeze totalLTE

> preorderNatLTE : Preorder Nat
> preorderNatLTE =
>   MkPreorder LTE reflexiveLTE transitiveLTE
> --%freeze preorderNatLTE

> totalPreorderNatLTE : TotalPreorder Nat
> totalPreorderNatLTE =
>   MkTotalPreorder LTE reflexiveLTE transitiveLTE totalLTE
> --%freeze totalPreorderNatLTE


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


Properties of |mult|

> multSuccNotZero : (m : Nat) -> (n : Nat) -> Not ((S m) * (S n) = Z)
> multSuccNotZero m  n  p = absurd p
> %freeze multSuccNotZero

> multNotZeroNotZero : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Not (n = Z) -> Not (m * n = Z)
> multNotZeroNotZero  Z     n    p q = void (p Refl)
> multNotZeroNotZero (S m)  Z    p q = void (q Refl)
> multNotZeroNotZero (S m) (S n) p q = multSuccNotZero m n
> %freeze multNotZeroNotZero

> multNotZeroNotZeroLeft : (m : Nat) -> (n : Nat) -> Not (m * n = Z) -> Not (m = Z)
> multNotZeroNotZeroLeft  Z     n    p = void (p (multZeroLeftZero n))
> multNotZeroNotZeroLeft (S m)  _    _ = SIsNotZ
> %freeze multNotZeroNotZeroLeft

> multNotZeroNotZeroRight : (m : Nat) -> (n : Nat) -> Not (m * n = Z) -> Not (n = Z)
> multNotZeroNotZeroRight m  Z     p = void (p (multZeroRightZero m))
> multNotZeroNotZeroRight _ (S n)  _ = SIsNotZ
> %freeze multNotZeroNotZeroRight

> multZeroLTZeroLT : (m : Nat) -> (n : Nat) -> Z `LT` m -> Z `LT` n -> Z `LT` (m * n)
> multZeroLTZeroLT  Z     n    p _ = absurd p
> multZeroLTZeroLT (S m)  Z    _ q = absurd q
> multZeroLTZeroLT (S m) (S n) _ _ = ltZS (n + m * (S n))
> %freeze multZeroLTZeroLT

> |||
> multLTZeroLeftLTZero : (m : Nat) -> (n : Nat) -> Z `LT` (m * n) -> Z `LT` m
> multLTZeroLeftLTZero Z n p = absurd p' where
>   p' : Z `LT` Z
>   p' = replace {x = Z * n}
>                {y = Z}
>                {P = \ ZUZU => Z `LT` ZUZU}
>                (multZeroLeftZero n) p
> multLTZeroLeftLTZero (S m) n _ = ltZS m
> %freeze multLTZeroLeftLTZero

> |||
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
> multFlipCentre : (m1 : Nat) -> (m2 : Nat) -> (n1 : Nat) -> (n2 : Nat) ->
>                  (m1 * m2) * (n1 * n2) = (m1 * n1) * (m2 * n2)
> multFlipCentre m1 m2 n1 n2 =
>   ( (m1 * m2) * (n1 * n2) )
> ={ multAssociative (m1 * m2) n1 n2 }=
>   ( ((m1 * m2) * n1) * n2 )
> ={ replace {x = (m1 * m2) * n1}
>            {y = m1 * (m2 * n1)}
>            {P = \ ZUZU => ((m1 * m2) * n1) * n2 = (ZUZU) * n2}
>            (sym (multAssociative m1 m2 n1)) Refl }=
>   ( (m1 * (m2 * n1)) * n2 )
> ={ replace {x = m2 * n1}
>            {y = n1 * m2}
>            {P = \ ZUZU => (m1 * (m2 * n1)) * n2 = (m1 * (ZUZU)) * n2 }
>            (multCommutative m2 n1) Refl }=
>   ( (m1 * (n1 * m2)) * n2 )
> ={ replace {x = m1 * (n1 * m2)}
>            {y = (m1 * n1) * m2}
>            {P = \ ZUZU => (m1 * (n1 * m2)) * n2 = (ZUZU) * n2}
>            (multAssociative m1 n1 m2) Refl }=
>   ( ((m1 * n1) * m2) * n2 )
> ={ sym (multAssociative (m1 * n1) m2 n2) }=
>   ( (m1 * n1) * (m2 * n2) )
> QED
> %freeze multPreservesEq


Decidability:

> ||| LTE is decidable
> decLTE : (m : Nat) -> (n : Nat) -> Dec (LTE m n)
> decLTE = lte
> {-
> decLTE Z _     = Yes LTEZero
> decLTE (S m) Z = No succNotLTEzero
> decLTE (S m) (S n) with (decLTE m n)
>   | (Yes p) = Yes (LTESucc p)
>   | (No contra) = No (\ p => contra (fromLteSucc p))
> -}
> -- %freeze decLTE

> ||| LT is decidable
> decLT : (m : Nat) -> (n : Nat) -> Dec (LT m n)
> decLT m n = decLTE (S m) n
> %freeze decLT


Uniqueness

> ||| LTE is unique
> uniqueLTE : (p1 : LTE m n) -> (p2 : LTE m n) -> p1 = p2
> uniqueLTE  LTEZero     LTEZero    = Refl
> uniqueLTE  LTEZero    (LTESucc p) impossible
> uniqueLTE (LTESucc p)  LTEZero    impossible
> uniqueLTE (LTESucc p) (LTESucc q) = cong (uniqueLTE p q)
> %freeze uniqueLTE

> ||| LT is unique
> uniqueLT : (p1 : LT m n) -> (p2 : LT m n) -> p1 = p2
> uniqueLT {m} {n} = uniqueLTE {m = S m} {n = n}
> %freeze uniqueLT

> |||
> uniqueLT' : m1 = m2 -> n1 = n2 -> (p1 : LT m1 n1) -> (p2 : LT m2 n2) -> p1 = p2
> uniqueLT' Refl Refl p1 p2 = uniqueLT p1 p2
> %freeze uniqueLT'


Properties of quotient:

> quotientLemma : (m : Nat) -> (d : Nat) -> (dDm : d `Divisor` m) -> d * (quotient m d dDm) = m
> quotientLemma m d (Evidence q prf) = prf
> %freeze quotientLemma

> quotientIsJustGetWitness : (m : Nat) -> (d : Nat) -> (dDm : d `Divisor` m) -> 
>                            quotient m d dDm = getWitness dDm
> quotientIsJustGetWitness m d (Evidence q prf) = 
>    ( quotient m d (Evidence q prf) )
>  ={ Refl }=
>    ( q )
>  ={ Refl }=
>    ( getWitness (Evidence q prf) )
>  QED
> %freeze quotientIsJustGetWitness

> ||| quotient preserves positivity
> quotientPreservesPositivity : (m : Nat) -> (d : Nat) -> (dDm : d `Divisor` m) -> 
>                               Z `LT` m -> Z `LT` (quotient m d dDm)
> quotientPreservesPositivity m d dDm zLTm = 
>   multLTZeroRightLTZero d q zLTdq where
>     q : Nat
>     q = quotient m d dDm
>     zLTdq : Z `LT` (d * q)
>     zLTdq = replace {x = m} 
>                     {y = d * q} 
>                     {P = \ ZUZU => Z `LT` ZUZU}  
>                     (sym (quotientLemma m d dDm)) zLTm
> %freeze quotientPreservesPositivity


Properties of Divisor:

> anyDivisorZ : (m : Nat) -> m `Divisor` Z
> anyDivisorZ m = Evidence Z (multZeroRightZero m)
> %freeze anyDivisorZ

> oneDivisorAny : (m : Nat) -> (S Z) `Divisor` m
> oneDivisorAny m = Evidence m (multOneLeftNeutral m)
> %freeze oneDivisorAny

> anyDivisorAny : (m : Nat) -> m `Divisor` m
> anyDivisorAny m = Evidence (S Z) (multOneRightNeutral m)
> %freeze anyDivisorAny

Divisor is a pre-order:

> divisorReflexive : (m : Nat) -> m `Divisor` m
> divisorReflexive = anyDivisorAny
> %freeze divisorReflexive

> divisorTransitive : l `Divisor` m -> m `Divisor` n -> l `Divisor` n
> divisorTransitive {l} {m} {n} (Evidence q1 p1) (Evidence q2 p2) = Evidence (q1 * q2) p where
>   s1 : (l * q1) * q2 = m * q2
>   s1 = multPreservesEq (l * q1) m q2 q2 p1 Refl
>   s2 : (l * q1) * q2 = n
>   s2 = trans s1 p2
>   p : l * (q1 * q2) = n
>   p = replace {x = (l * q1) * q2}
>               {y = l * (q1 * q2)}
>               {P = \ ZUZU => ZUZU = n}
>               (sym (multAssociative l q1 q2)) s2
> %freeze divisorTransitive

> divisorAntisymmetric : (m : Nat) -> (n : Nat) -> m `Divisor` n -> n `Divisor` m -> m = n
> divisorAntisymmetric  Z     Z     _                _               = Refl
> divisorAntisymmetric  Z    (S n) (Evidence q1 p1)  _               = absurd p1
> divisorAntisymmetric (S m)  Z     _               (Evidence q2 p2) = absurd p2
> divisorAntisymmetric (S m) (S n) (Evidence q1 p1) (Evidence q2 p2) = s8 where
>   s1 : (S m) * q1 = S n
>   s1 = p1
>   s2 : (S n) * q2 = S m
>   s2 = p2
>   s3 : ((S n) * q2) * q1 = S n
>   s3 = replace {x = S m}
>                {y = (S n) * q2}
>                {P = \ZUZU => ZUZU * q1 = S n}
>                (sym s2)
>                s1
>   s4 : (S n) * (q2 * q1) = S n
>   s4 = replace {x = ((S n) * q2) * q1}
>                {y = (S n) * (q2 * q1)}
>                {P = \ ZUZU => ZUZU = S n}
>                (sym (multAssociative (S n) q2 q1) ) s3
>   s5 : q2 * q1 = S Z
>   s5 = multElim1 n (q2 * q1) s4
>   s6 : q1 = S Z
>   s6 = multOneRightOne q2 q1 s5
>   s7 : (S m) * (S Z) = S n
>   s7 = replace {x = q1}
>                {y = S Z}
>                {P = \ ZUZU => (S m) * ZUZU = S n}
>                s6 s1
>   s8 : S m  = S n
>   s8 = replace {x = (S m) * (S Z)}
>                {y = S m}
>                {P = \ ZUZU => ZUZU = S n}
>                (multOneRightNeutral (S m)) s7
> %freeze divisorAntisymmetric

> divisorPlusLemma1 : (m : Nat) -> (n : Nat) -> (d : Nat) ->
>                     d `Divisor` m -> d `Divisor` n -> d `Divisor` (m + n)
> divisorPlusLemma1 m n d (Evidence q1 p1) (Evidence q2 p2) =
>   Evidence (q1 + q2) p where
>     s1 : d * (q1 + q2) = d * q1 + d * q2
>     s1 = multDistributesOverPlusRight d q1 q2
>     s2 : d * (q1 + q2) = m + d * q2
>     s2 = replace {x = d * q1} {y = m} {P = \ ZUZU => d * (q1 + q2) = ZUZU + d * q2} p1 s1
>     p : d * (q1 + q2) = m + n
>     p = replace {x = d * q2} {y = n} {P = \ ZUZU => d * (q1 + q2) = m + ZUZU} p2 s2
> --%freeze divisorPlusLemma1

> divisorPlusLemma2 : (m : Nat) -> (n : Nat) -> (d : Nat) ->
>                      d `Divisor` m -> d `Divisor` n -> d `Divisor` (n + m)
> divisorPlusLemma2 m n d (Evidence q1 p1) (Evidence q2 p2) =
>   Evidence (q1 + q2) p where
>     s1 : d * (q1 + q2) = d * q1 + d * q2
>     s1 = multDistributesOverPlusRight d q1 q2
>     s2 : d * (q1 + q2) = m + d * q2
>     s2 = replace {x = d * q1} {y = m} {P = \ ZUZU => d * (q1 + q2) = ZUZU + d * q2} p1 s1
>     s3 : d * (q1 + q2) = m + n
>     s3 = replace {x = d * q2} {y = n} {P = \ ZUZU => d * (q1 + q2) = m + ZUZU} p2 s2
>     p  : d * (q1 + q2) = n + m
>     p  = replace {x = m + n} {y = n + m} {P = \ ZUZU => d * (q1 + q2) = ZUZU} (plusCommutative m n) s3
> %freeze divisorPlusLemma2

> divisorMultLemma1 : (m1 : Nat) -> (d1 : Nat) -> d1 `Divisor` m1 -> 
>                     (m2 : Nat) -> (d2 : Nat) -> d2 `Divisor` m2 -> 
>                     (d1 * d2) `Divisor` (m1 * m2)
> divisorMultLemma1 m1 d1 (Evidence q1 p1) m2 d2 (Evidence q2 p2) = 
>   Evidence (q1 * q2) p where
>     s1 : (d1 * q1) * (d2 * q2) = m1 * m2
>     s1 = multPreservesEq (d1 * q1) m1 (d2 * q2) m2 p1 p2
>     p  : (d1 * d2) * (q1 * q2) = m1 * m2
>     p  = replace {x = (d1 * q1) * (d2 * q2)}
>                  {y = (d1 * d2) * (q1 * q2)}
>                  {P = \ ZUZU => ZUZU = m1 * m2}
>                  (multFlipCentre d1 q1 d2 q2) s1
> -- %freeze divisorMultLemma1

> ||| If a number divides two numbers, it also divides their difference
> divisorMinusLemma : (m : Nat) -> (n : Nat) -> (d : Nat) ->
>                     d `Divisor` m -> d `Divisor` n -> d `Divisor` (n - m)
> divisorMinusLemma m n d (Evidence q1 p1) (Evidence q2 p2) =
>   Evidence q p where
>     q : Nat
>     q = q2 - q1
>     p : d * q = n - m
>     p = s2 where
>       s1 : d * q2 - d * q1 = n - m
>       s1 = cong2 minus p2 p1
>       s2 : d * (q2 - q1) = n - m
>       s2 = replace {x = d * q2 - d * q1}
>                    {y = d * (q2 - q1)}
>                    {P = \ZUZU => ZUZU = n - m}
>                    (sym (multDistributesOverMinusRight d q2 q1))
>                    s1
> %freeze divisorMinusLemma

> divisorOneLemma : (d : Nat) -> (d' : Nat) -> (S d) * d' `Divisor` (S d) -> d' `Divisor` S Z
> divisorOneLemma d d' (Evidence q p) =
>   Evidence q p' where
>     s1 : ((S d) * d') * q = S d
>     s1 = p
>     s2 : (S d) * (d' * q) = S d
>     s2 = replace {x = ((S d) * d') * q} {y = (S d) * (d' * q)} {P = \ ZUZU => ZUZU = S d} (sym (multAssociative (S d) d' q)) s1
>     p' : d' * q = S Z
>     p' = multElim1 d (d' * q) s2
> %freeze divisorOneLemma

> divisorOneLemma' : (d : Nat) -> (d' : Nat) -> Not (d = Z) -> d * d' `Divisor` d -> d' `Divisor` S Z
> divisorOneLemma'  Z    _  dNotZ _  = void (dNotZ Refl)
> divisorOneLemma' (S d) d' dNotZ (Evidence q p) =
>   Evidence q p' where
>     s1 : ((S d) * d') * q = S d
>     s1 = p
>     s2 : (S d) * (d' * q) = S d
>     s2 = replace {x = ((S d) * d') * q} {y = (S d) * (d' * q)} {P = \ ZUZU => ZUZU = S d} (sym (multAssociative (S d) d' q)) s1
>     p' : d' * q = S Z
>     p' = multElim1 d (d' * q) s2
> %freeze divisorOneLemma'

> |||
> divisorTowerLemma: (d : Nat) -> (d' : Nat) -> (m : Nat) ->
>                    (dDm : d `Divisor` m) -> d' `Divisor` (quotient m d dDm) -> d * d' `Divisor` m
> divisorTowerLemma d d' m dDm d'DmOd = Evidence q' p where
>   q' : Nat
>   q' = quotient (quotient m d dDm) d' d'DmOd
>   s1 : d' * q' = quotient m d dDm
>   s1 = quotientLemma (quotient m d dDm) d' d'DmOd
>   s2 : d * (quotient m d dDm) = m
>   s2 = quotientLemma m d dDm
>   s3 : d * (d' * q') = m
>   s3 = replace {x = quotient m d dDm} {y = d' * q'} {P = \ ZUZU => d * ZUZU = m} (sym s1) s2
>   p : (d * d') * q' = m
>   p = replace {x = d * (d' * q')} {y = (d * d') * q'} {P = \ ZUZU => ZUZU = m} (multAssociative d d' q') s3
> %freeze divisorTowerLemma


Further quotient properties:

> |||
> quotientAnyOneAny : (m : Nat) -> (d : Nat) -> (dDm : d `Divisor` m) -> 
>                     (d = S Z) -> quotient m d dDm = m
> quotientAnyOneAny m d (Evidence q p) dEQ1 = 
>     ( quotient m d (Evidence q p) )
>   ={ Refl }=
>     ( q )
>   ={ sym (multOneLeftNeutral q) }=
>     ( (S Z) * q )
>   ={ replace {x = S Z}
>              {y = d}
>              {P = \ ZUZU => (S Z) * q = ZUZU * q}
>              (sym dEQ1) Refl }=
>     ( d * q )
>   ={ p }=
>     ( m )
>   QED

> |||
> quotientPlusLemma : (m : Nat) -> (n : Nat) -> (d : Nat) -> 
>                     (dDm : d `Divisor` m) -> (dDn : d `Divisor` n) ->
>                     (quotient m d dDm) + (quotient n d dDn) 
>                     =
>                     quotient (m + n) d (divisorPlusLemma1 m n d dDm dDn)
> quotientPlusLemma m n d (Evidence q1 p1) (Evidence q2 p2) =
>     ( (quotient m d (Evidence q1 p1)) + (quotient n d (Evidence q2 p2)) )
>   ={ Refl }=
>     ( q1 + q2 )
>   ={ Refl }=
>     ( quotient (m + n) d (divisorPlusLemma1 m n d (Evidence q1 p1) (Evidence q2 p2)) )
>   QED

> |||
> quotientMultLemma : (m1 : Nat) -> (d1 : Nat) -> (d1Dm1 : d1 `Divisor` m1) ->
>                     (m2 : Nat) -> (d2 : Nat) -> (d2Dm2 : d2 `Divisor` m2) ->
>                     (quotient m1 d1 d1Dm1) * (quotient m2 d2 d2Dm2) 
>                     =
>                     quotient (m1 * m2) (d1 * d2) (divisorMultLemma1 m1 d1 d1Dm1 m2 d2 d2Dm2)
> quotientMultLemma m1 d1 (Evidence q1 p1) m2 d2 (Evidence q2 p2) =
>     ( (quotient m1 d1 (Evidence q1 p1)) * (quotient m2 d2 (Evidence q2 p2))  )
>   ={ Refl }=
>     ( q1 * q2 )
>   ={ Refl }=
>     ( quotient (m1 * m2) (d1 * d2) (divisorMultLemma1 m1 d1 (Evidence q1 p1) m2 d2 (Evidence q2 p2)) )
>   QED

> |||
> quotientCancellationLemma : (m : Nat) -> (d : Nat) -> 
>                             (sdDsdm : (S d) `Divisor` (S d) * m) -> 
>                             quotient ((S d) * m) (S d) sdDsdm = m
> quotientCancellationLemma m d (Evidence q prf) = 
>     ( q )
>   ={ multMultElimLeft (S d) (S d) q m Refl SIsNotZ prf }=
>     ( m )
>   QED
   
> |||
> quotientDivisorLemma : (d : Nat) -> (m : Nat) -> (n : Nat) ->
>                        (sdDm : S d `Divisor` m) ->
>                        (mDn: m `Divisor` n) -> 
>                        (sdDn : S d `Divisor` n) ->
>                        (quotient m (S d) sdDm) `Divisor` (quotient n (S d) sdDn)
> quotientDivisorLemma d m n (Evidence x sdxEQm) (Evidence y myEQn) (Evidence z sdzEQn) = 
>   Evidence y xyEQz where
>     sdxyEQmy    :  ((S d) * x) * y = m * y
>     sdxyEQmy    =  multPreservesEq ((S d) * x) m y y sdxEQm Refl
>     sdxyEQsdz   :  ((S d) * x) * y = (S d) * z
>     sdxyEQsdz   =  trans sdxyEQmy (trans myEQn (sym sdzEQn))
>     sdxyEQsdz'  :  (S d) * (x * y) = (S d) * z
>     sdxyEQsdz'  =  replace {x = ((S d) * x) * y}
>                            {y = (S d) * (x * y)}
>                            {P = \ ZUZU => ZUZU = (S d) * z}
>                            (sym (multAssociative (S d) x y)) sdxyEQsdz
>     xyEQz       :  x * y = z
>     xyEQz       =  multMultElimLeft (S d) (S d) (x * y) z Refl SIsNotZ sdxyEQsdz'
   
> |||
> quotientDivisorLemma1 : (a : Nat) -> (b : Nat) -> (c : Nat) ->
>                         (saDb : S a `Divisor` b) ->
>                         (bDc  :   b `Divisor` c) -> 
>                         (quotient b (S a) saDb) 
>                         `Divisor` 
>                         (quotient c (S a) (divisorTransitive {l = S a} {m = b} {n = c} saDb bDc))
> quotientDivisorLemma1 a b c saDb bDc = prf where
>   x           :  Nat
>   x           =  getWitness saDb
>   saxEQb      :  (S a) * x = b
>   saxEQb      =  getProof saDb
>   y           :  Nat
>   y           =  getWitness bDc
>   byEQc       :  b * y = c
>   byEQc       =  getProof bDc
>   saDc        :  (S a) `Divisor` c
>   saDc        =  divisorTransitive {l = S a} {m = b} {n = c} saDb bDc
>   z           :  Nat
>   z           =  getWitness saDc
>   sazEQc      :  (S a) * z = c
>   sazEQc      =  getProof saDc 
>   saxyEQby    :  ((S a) * x) * y = b * y
>   saxyEQby    =  multPreservesEq ((S a) * x) b y y saxEQb Refl
>   saxyEQsaz   :  ((S a) * x) * y = (S a) * z
>   saxyEQsaz   =  trans saxyEQby (trans byEQc (sym sazEQc))
>   saxyEQsaz'  :  (S a) * (x * y) = (S a) * z
>   saxyEQsaz'  =  replace {x = ((S a) * x) * y}
>                          {y = (S a) * (x * y)}
>                          {P = \ ZUZU => ZUZU = (S a) * z}
>                          (sym (multAssociative (S a) x y)) saxyEQsaz
>   xyEQz       :  x * y = z
>   xyEQz       =  multMultElimLeft (S a) (S a) (x * y) z Refl SIsNotZ saxyEQsaz'
>   prf1        :  x `Divisor` z
>   prf1        =  Evidence y xyEQz
>   prf2        :  (quotient b (S a) saDb)  `Divisor` z
>   prf2        =  replace {x = x}
>                          {y = quotient b (S a) saDb}
>                          {P = \ ZUZU => ZUZU `Divisor` z}
>                          (sym (quotientIsJustGetWitness b (S a) saDb)) prf1
>   prf         :  (quotient b (S a) saDb) `Divisor` (quotient c (S a) saDc)
>   prf         =  replace {x = z}
>                          {y = quotient c (S a) (divisorTransitive {l = S a} {m = b} {n = c} saDb bDc)}
>                          {P = \ ZUZU => (quotient b (S a) saDb) `Divisor` ZUZU}
>                          (sym (quotientIsJustGetWitness c (S a) saDc)) prf2


Greatest common divisor properties:

> gcdUnique : (d1 : Nat) -> (d2 : Nat) -> GCD d1 m n -> GCD d2 m n -> d1 = d2
> gcdUnique d1 d2 (MkGCD d1Dm d1Dn d1G) (MkGCD d2Dm d2Dn d2G) = s3 where
>   s1 : d1 `Divisor` d2
>   s1 = d2G d1 d1Dm d1Dn
>   s2 : d2 `Divisor` d1
>   s2 = d1G d2 d2Dm d2Dn
>   s3 : d1 = d2
>   s3 = divisorAntisymmetric d1 d2 s1 s2
> %freeze gcdUnique

> ||| If |m| is positive, the greatest common divisor of |m| and |n| is positive
> gcdPreservesPositivity1 : Z `LT` m -> (dv : (d : Nat ** GCD d m n)) -> Z `LT` (getWitness dv)
> gcdPreservesPositivity1 {m} zLTm (d ** prf) = multLTZeroLeftLTZero d q zLTdq where
>   dDm : d `Divisor` m
>   dDm = gcdDivisorFst prf
>   q : Nat
>   q = quotient m d dDm
>   zLTdq : Z `LT` (d * q)
>   zLTdq = replace {x = m} 
>                   {y = d * q} 
>                   {P = \ ZUZU => Z `LT` ZUZU}  
>                   (sym (quotientLemma m d dDm)) zLTm 
> %freeze gcdPreservesPositivity1

> ||| If |n| is positive, the greatest common divisor of |m| and |n| is positive
> gcdPreservesPositivity2 : Z `LT` n -> (dv : (d : Nat ** GCD d m n)) -> Z `LT` (getWitness dv)
> gcdPreservesPositivity2 {n} zLTn (d ** prf) = multLTZeroLeftLTZero d q zLTdq where
>   dDn : d `Divisor` n
>   dDn = gcdDivisorSnd prf
>   q : Nat
>   q = quotient n d dDn
>   zLTdq : Z `LT` (d * q)
>   zLTdq = replace {x = n} 
>                   {y = d * q} 
>                   {P = \ ZUZU => Z `LT` ZUZU}  
>                   (sym (quotientLemma n d dDn)) zLTn 
> %freeze gcdPreservesPositivity2

> ||| 
> gcdLemma : (v : GCD (S d) m n) ->
>            d' `Divisor` (quotient m (S d) (gcdDivisorFst v)) ->
>            d' `Divisor` (quotient n (S d) (gcdDivisorSnd v)) ->
>            d' `Divisor` S Z
> gcdLemma {d} {d'} {m} {n} v d'DmoSd d'DnoSd = divisorOneLemma d d' Sdd'DSd where
>   SdDm    : (S d) `Divisor` m
>   SdDm    = gcdDivisorFst v
>   SdDn    : (S d) `Divisor` n
>   SdDn    = gcdDivisorSnd v
>   SdG     : (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` (S d)
>   SdG     = gcdDivisorGreatest v
>   Sdd'Dm  : (S d) * d' `Divisor` m
>   Sdd'Dm  = divisorTowerLemma (S d) d' m SdDm d'DmoSd
>   Sdd'Dn  : (S d) * d' `Divisor` n
>   Sdd'Dn  = divisorTowerLemma (S d) d' n SdDn d'DnoSd
>   Sdd'DSd : (S d) * d' `Divisor` (S d)
>   Sdd'DSd = SdG ((S d) * d') Sdd'Dm Sdd'Dn
> %freeze gcdLemma

> gcdLemma' : (v : GCD d m n) -> Not (d = Z) ->
>             d' `Divisor` (quotient m d (gcdDivisorFst v)) ->
>             d' `Divisor` (quotient n d (gcdDivisorSnd v)) ->
>             d' `Divisor` S Z
> gcdLemma' {d} {d'} {m} {n} v dNotZ d'DmoSd d'DnoSd = divisorOneLemma' d d' dNotZ Sdd'DSd where
>   SdDm    : d `Divisor` m
>   SdDm    = gcdDivisorFst v
>   SdDn    : d `Divisor` n
>   SdDn    = gcdDivisorSnd v
>   SdG     : (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d
>   SdG     = gcdDivisorGreatest v
>   Sdd'Dm  : d * d' `Divisor` m
>   Sdd'Dm  = divisorTowerLemma d d' m SdDm d'DmoSd
>   Sdd'Dn  : d * d' `Divisor` n
>   Sdd'Dn  = divisorTowerLemma d d' n SdDn d'DnoSd
>   Sdd'DSd : d * d' `Divisor` d
>   Sdd'DSd = SdG (d * d') Sdd'Dm Sdd'Dn
> %freeze gcdLemma'

> ||| d GCD ((S a) * m) ((S a) * n) => d/(S a) GCD m n
> ||| 
> ||| The implementation is based on a proof by Tim Richter. We have to show
> |||
> |||   1) d/(S a) is a divisor of m
> |||   2) d/(S a) is a divisor of n
> |||   3) if d' is a divisor of m and n, then d' is a divisor of d/(S a)
> ||| 
> ||| We know from |quotientDivisorLemma| that
> |||   
> |||   a|b, b|c, a|c => (b/a)|(c/a)
> |||
> ||| Thus, we can prove 1) and 2) by applying the lemma to
> |||
> |||   (S a)|d, d|((S a) * m), (S a)|((S a) * m)
> |||
> |||   and
> |||
> |||   (S a)|d, d|((S a) * n), (S a)|((S a) * n)
> |||
> ||| and using |quotientCancellationLemma| to reduce ((S a) * m)/(S a) and
> ||| ((S a) * n)/(S a) to m and n, respectively. Since d is the GCD of 
> ||| (S a) * m and (S a) * n and (S a) is trivially a divisor of both, we
> ||| readily have (S a)|d. d|((S a) * m) and d|((S a) * m) also diretly follow
> ||| from d being the GCD of (S a) * m and (S a) * n. 
> |||
> ||| In order to prove 3), we again apply |quotientDivisorLemma|, this time to
> ||| 
> |||   (S a)|((S a) * d'), ((S a) * d')|d, (S a)|d
> |||
> ||| We derive ((S a) * d')|d from the hypothesis d'|m, d'|n by pre-multiplying
> ||| by (S a) (and using |divisorMultLemma1|). This yields
> |||
> |||   ((S a) * d')|((S a) * m), ((S a) * d')|((S a) * n)
> |||
> ||| The result directly follows from d being the GCD of (S a) * m and (S a) * n.
> |||
> gcdDivisorLemma : (d : Nat) -> (m : Nat) -> (n : Nat) -> (a : Nat) ->
>                   GCD d ((S a) * m) ((S a) * n) -> 
>                   (saDd : (S a) `Divisor` d ** GCD (quotient d (S a) saDd) m n)

> gcdDivisorLemma d m n a v = (saDd ** MkGCD qDm qDn qG) where
>   dDsam   :  d `Divisor` ((S a) * m)
>   dDsam   =  gcdDivisorFst v
>   saDsam  :  S a `Divisor` ((S a) * m)
>   saDsam  =  Evidence m Refl
>   dDsan   :  d `Divisor` ((S a) * n)
>   dDsan   =  gcdDivisorSnd v
>   saDsan  :  S a `Divisor` ((S a) * n)
>   saDsan  =  Evidence n Refl
>   saDd    :  (S a) `Divisor` d
>   saDd    =  gcdDivisorGreatest {d = d} v (S a) saDsam saDsan

>   q       :  Nat
>   q       =  quotient d (S a) saDd
>   preqDm  :  q `Divisor` (quotient ((S a) * m) (S a) saDsam)
>   preqDm  =  quotientDivisorLemma a d ((S a) * m) saDd dDsam saDsam
>   qDm     :  q `Divisor` m
>   qDm     =  replace {x = quotient ((S a) * m) (S a) saDsam}
>                      {y = m}
>                      {P = \ ZUZU => q `Divisor` ZUZU}
>                      (quotientCancellationLemma m a saDsam) preqDm
    
>   preqDn  :  q `Divisor` (quotient ((S a) * n) (S a) saDsan)
>   preqDn  =  quotientDivisorLemma a d ((S a) * n) saDd dDsan saDsan
>   qDn     :  q `Divisor` n
>   qDn     =  replace {x = quotient ((S a) * n) (S a) saDsan}
>                      {y = n}
>                      {P = \ ZUZU => q `Divisor` ZUZU}
>                      (quotientCancellationLemma n a saDsan) preqDn
   
>   preqG   :  (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> 
>              (quotient ((S a) * d') (S a) (Evidence d' Refl)) `Divisor` q
>   preqG d' d'Dm d'Dn  =  quotientDivisorLemma a ((S a) * d') d (Evidence d' Refl) sad'Dd saDd
>     where sad'Dsam  :  ((S a) * d') `Divisor` ((S a) * m)
>           sad'Dsam  =  divisorMultLemma1 (S a) (S a) (anyDivisorAny (S a)) m d' d'Dm
>           sad'Dsan  :  ((S a) * d') `Divisor` ((S a) * n)
>           sad'Dsan  =  divisorMultLemma1 (S a) (S a) (anyDivisorAny (S a)) n d' d'Dn
>           sad'Dd    :  ((S a) * d') `Divisor` d
>           sad'Dd    =  gcdDivisorGreatest {d = d} v ((S a) * d') sad'Dsam sad'Dsan
>
>   qG      :  (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` q
>   qG    d' d'Dm d'Dn     =  replace {x = quotient ((S a) * d') (S a) (Evidence d' Refl)}
>                                     {y = d'}
>                                     {P = \ ZUZU => ZUZU `Divisor` q}
>                                     (quotientCancellationLemma d' a (Evidence d' Refl)) (preqG d' d'Dm d'Dn)

> gcdScaleInvariant : (d : Nat) -> (m : Nat) -> (n : Nat) -> (d' : Nat) -> (a : Nat) ->
>                     GCD d m n -> GCD d' (a * m) (a * n) -> d' = a * d
> gcdScaleInvariant d m n d'  Z    v  v' = s6 where
>   s0   :  Z `Divisor` (Z * m)
>   s0   =  Evidence m Refl
>   s1   :  Z `Divisor` (Z * n)
>   s1   =  Evidence n Refl
>   s2   :  Z `Divisor` d'
>   s2   =  gcdDivisorGreatest {d = d'} v' Z s0 s1
>   s3   :  Nat
>   s3   =  getWitness s2
>   s4   :  Z * s3 = d'
>   s4   =  getProof s2
>   s5   :  d' = Z
>   s5   =  replace {x = Z * s3} {y = Z} {P = \ ZUZU => d' = ZUZU} (multZeroLeftZero s3) (sym s4)
>   s6   :  d' = Z * d
>   s6   =  replace {x = Z} {y = Z * d} {P = \ ZUZU => d' = ZUZU} (sym (multZeroLeftZero d)) s5
> gcdScaleInvariant d m n d' (S a) v  v' = s4 where
>   s0   :  (S a) `Divisor` d'
>   s0   =  getWitness (gcdDivisorLemma d' m n a v')
>   s1   :  GCD (quotient d' (S a) s0) m n 
>   s1   =  getProof (gcdDivisorLemma d' m n a v')
>   s2   :  quotient d' (S a) s0 = d
>   s2   =  gcdUnique (quotient d' (S a) s0) d s1 v
>   s3   :  (S a) * (quotient d' (S a) s0) = (S a) * d
>   s3   =  multPreservesEq (S a) (S a) (quotient d' (S a) s0) d Refl s2
>   s4   :  d' = (S a) * d
>   s4   =  replace {x = (S a) * (quotient d' (S a) s0)}
>                   {y = d'}
>                   {P = \ ZUZU => ZUZU = (S a) * d}
>                   (quotientLemma d' (S a) s0) s3


Coprime properties:

> ||| Coprime is decidable
> decCoprime : ((a : Nat) -> (b : Nat) -> (d : Nat ** GCD d a b)) ->
>              (m : Nat) -> (n : Nat) ->
>              Dec (Coprime m n)
> decCoprime alg m n with (alg m n)
>   | (d ** v) with (decEq d (S Z))
>     | (Yes p) = Yes (MkCoprime {d = d} v p)
>     | (No contra) = No contra' where
>         contra' : Coprime m n -> Void
>         contra' (MkCoprime {d = d'} v' p') = contra p where
>           p : d = S Z
>           p = replace {x = d'}
>                       {y = d}
>                       {P = \ ZUZU => ZUZU = S Z}
>                       (gcdUnique d' d v' v) p'
> %freeze decCoprime

> ||| Coprime is symmetric
> symmetricCoprime : Coprime m n -> Coprime n m
> symmetricCoprime {m} {n} (MkCoprime (MkGCD {d} {m} {n} dDm dDn dG)  dEQone) =
>                          (MkCoprime (MkGCD             dDn dDm dG') dEQone) where
>     dG' : (d' : Nat) -> Divisor d' n -> Divisor d' m -> Divisor d' d
>     dG' d' d'Dn d'Dm = dG d' d'Dm d'Dn
> %freeze symmetricCoprime

> ||| Any number is coprime with one
> anyCoprimeOne : Coprime m (S Z)
> anyCoprimeOne {m} = MkCoprime (MkGCD oDm oDo oG) Refl where
>   oDm : (S Z) `Divisor` m
>   oDm = oneDivisorAny m
>   oDo : (S Z) `Divisor` (S Z)
>   oDo = anyDivisorAny (S Z)
>   oG  : (d : Nat) -> d `Divisor` m -> d `Divisor` (S Z) -> d `Divisor` (S Z)
>   oG d dDm dDo = dDo
> %freeze anyCoprimeOne

> ||| Division by gcd yields coprime numbers
> gcdCoprimeLemma : (v : GCD (S d) m n) -> Coprime (quotient m (S d) (gcdDivisorFst v))
>                                                  (quotient n (S d) (gcdDivisorSnd v))
> gcdCoprimeLemma {d} {m} {n} v = MkCoprime (MkGCD d'Dm' d'Dn' d'G) Refl where
>   dDm     : (S d) `Divisor` m
>   dDm     = gcdDivisorFst v
>   dDn     : (S d) `Divisor` n
>   dDn     = gcdDivisorSnd v
>   m'      : Nat
>   m'      = quotient m (S d) dDm
>   n'      : Nat
>   n'      = quotient n (S d) dDn
>   d'Dm'   : S Z `Divisor` m'
>   d'Dm'   = oneDivisorAny m'
>   d'Dn'   : S Z `Divisor` n'
>   d'Dn'   = oneDivisorAny n'
>   d'G     : (d'' : Nat) -> d'' `Divisor` m' -> d'' `Divisor` n' -> d'' `Divisor` (S Z)
>   d'G d'' = gcdLemma v
> %freeze gcdCoprimeLemma

> ||| Division by gcd yields coprime numbers
> gcdCoprimeLemma' : (v : GCD d m n) -> Not (d = Z) -> Coprime (quotient m d (gcdDivisorFst v))
>                                                              (quotient n d (gcdDivisorSnd v))
> gcdCoprimeLemma' {d} {m} {n} v dNotZ = MkCoprime (MkGCD d'Dm' d'Dn' d'G) Refl where
>   dDm     : d `Divisor` m
>   dDm     = gcdDivisorFst v
>   dDn     : d `Divisor` n
>   dDn     = gcdDivisorSnd v
>   m'      : Nat
>   m'      = quotient m d dDm
>   n'      : Nat
>   n'      = quotient n d dDn
>   d'Dm'   : S Z `Divisor` m'
>   d'Dm'   = oneDivisorAny m'
>   d'Dn'   : S Z `Divisor` n'
>   d'Dn'   = oneDivisorAny n'
>   d'G     : (d'' : Nat) -> d'' `Divisor` m' -> d'' `Divisor` n' -> d'' `Divisor` (S Z)
>   d'G d'' = gcdLemma' v dNotZ
> %freeze gcdCoprimeLemma'

> ||| Division by gcd yields coprime numbers
> gcdCoprimeLemma'' : (v : GCD d m n) -> Z `LT` d -> Coprime (quotient m d (gcdDivisorFst v))
>                                                            (quotient n d (gcdDivisorSnd v))
> gcdCoprimeLemma'' {d} {m} {n} v zLTd = MkCoprime (MkGCD d'Dm' d'Dn' d'G) Refl where
>   dDm     : d `Divisor` m
>   dDm     = gcdDivisorFst v
>   dDn     : d `Divisor` n
>   dDn     = gcdDivisorSnd v
>   m'      : Nat
>   m'      = quotient m d dDm
>   n'      : Nat
>   n'      = quotient n d dDn
>   d'Dm'   : S Z `Divisor` m'
>   d'Dm'   = oneDivisorAny m'
>   d'Dn'   : S Z `Divisor` n'
>   d'Dn'   = oneDivisorAny n'
>   dNotZ   : Not (d = Z)
>   dNotZ   = gtZisnotZ zLTd
>   d'G     : (d'' : Nat) -> d'' `Divisor` m' -> d'' `Divisor` n' -> d'' `Divisor` (S Z)
>   d'G d'' = gcdLemma' v dNotZ
> %freeze gcdCoprimeLemma''


GCD / Coprime properties:

> |||
> gcdOneCoprimeLemma1 : (alg : (a : Nat) -> (b : Nat) -> (d : Nat ** GCD d a b)) ->
>                       (m : Nat) -> (n : Nat) ->
>                       gcd (alg m n) = S Z -> Coprime m n
> gcdOneCoprimeLemma1 alg m n prf = MkCoprime (getProof (alg m n)) prf
> %freeze gcdOneCoprimeLemma1

> |||
> gcdOneCoprimeLemma2 : (m : Nat) -> (n : Nat) ->
>                       (alg : (a : Nat) -> (b : Nat) -> (d : Nat ** GCD d a b)) ->
>                       Coprime m n -> gcd (alg m n) = S Z
> gcdOneCoprimeLemma2 m n alg (MkCoprime {d} v prf) = s3 where
>   s1 : d = S Z
>   s1 = prf
>   s2 : gcd (alg m n) = d
>   s2 = gcdUnique (gcd (alg m n)) d (getProof (alg m n)) v
>   s3 : gcd (alg m n) = S Z
>   s3 = trans s2 s1
> %freeze gcdOneCoprimeLemma2

> |||
> gcdAnyOneOne : (alg : (a : Nat) -> (b : Nat) -> (d : Nat ** GCD d a b)) ->
>                (m : Nat) ->
>                gcd (alg m (S Z)) = S Z
> gcdAnyOneOne alg m = gcdOneCoprimeLemma2 m (S Z) alg anyCoprimeOne
> %freeze gcdAnyOneOne

> {-

> ---}
