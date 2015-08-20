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

> succInjective' : (left : Nat) -> (right : Nat) -> Not (left = right) -> Not (S left = S right)
> succInjective' left right contra = contra . (succInjective left right)


LT, LTE properties

> notLTELemma0 : Not (S m `LTE` S n) -> Not (m `LTE` n)
> notLTELemma0 contra = contra . LTESucc

> notLTELemma1 : (m : Nat) -> (n : Nat) -> Not (m `LTE` n) -> n `LTE` m 
> notLTELemma1  m     Z    p = LTEZero
> notLTELemma1  Z    (S n) p = void (p LTEZero)
> notLTELemma1 (S m) (S n) p = LTESucc (notLTELemma1 m n (notLTELemma0 p))

> |||
> lteLemma1 : (m : Nat) -> (n : Nat) -> LTE (S m) n -> LTE m n
> lteLemma1  Z     Z             prf  = absurd prf
> lteLemma1  Z    (S n)  LTEZero        impossible
> lteLemma1  Z    (S n) (LTESucc prf) = LTEZero
> lteLemma1 (S m)  Z             prf  = absurd prf
> lteLemma1 (S m) (S n)  LTEZero        impossible
> lteLemma1 (S m) (S n) (LTESucc prf) = LTESucc (lteLemma1 m n prf)


> |||
> ltLemma1 : (m : Nat) -> (n : Nat) -> LT (S m) n -> LT m n
> ltLemma1 m n prf = lteLemma1 (S m) n prf


> ||| LT is contained in LTE
> ltInLTE : (m : Nat) -> (n : Nat) -> LT m n -> LTE m n
> ltInLTE = lteLemma1


> ||| EQ is contained in LTE
> eqInLTE : (m : Nat) -> (n : Nat) -> m = n -> m `LTE` n
> eqInLTE  Z     n    prf = LTEZero
> eqInLTE (S m)  Z    prf = absurd prf
> eqInLTE (S m) (S n) prf = LTESucc (eqInLTE m n (succInjective m n prf))


> |||
> idSuccPreservesLTE : (m : Nat) -> (n : Nat) -> m `LTE` n -> m `LTE` (S n)
> idSuccPreservesLTE  Z     n    prf = LTEZero
> idSuccPreservesLTE (S m)  Z    prf = absurd prf
> idSuccPreservesLTE (S m) (S n) prf = LTESucc (idSuccPreservesLTE m n (fromLteSucc prf))


> ||| Zero is smaller than any successor
> ltZS : (m : Nat) -> LT Z (S m)
> ltZS  Z    = LTESucc LTEZero
> ltZS (S m) = idSuccPreservesLTE (S Z) (S m) (ltZS m)


> ||| Any number is smaller than its successor
> ltIdS : (m : Nat) -> LT m (S m)
> ltIdS  Z    = LTESucc LTEZero
> ltIdS (S m) = LTESucc (ltIdS m)


> ||| Any number which is not zero is greater than zero
> notZisgtZ : {n : Nat} -> Not (n = Z) -> LT Z n
> notZisgtZ {n = Z}   contra = void (contra Refl)
> notZisgtZ {n = S m} _      = ltZS m


> ||| Any number which is greater than zero is not zero
> gtZisnotZ : {n : Nat} -> LT Z n -> Not (n = Z)
> gtZisnotZ {n = Z}   p = absurd p
> gtZisnotZ {n = S m} p = absurd


> ||| No number is less than zero
> notLTzero : {n : Nat} -> Not (LT n Z)
> notLTzero = succNotLTEzero


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

> monotoneNatPlusLTE : {x : Nat} -> {y : Nat} ->
>                      (z : Nat) -> LTE x y -> LTE (z + x) (z + y)
> monotoneNatPlusLTE {x} {y}  Z    xLTEy = xLTEy
> monotoneNatPlusLTE {x} {y} (S n) xLTEy = LTESucc (monotoneNatPlusLTE {x} {y} n xLTEy)



> reflexiveLTE : (n : Nat) -> LTE n n
> reflexiveLTE n = lteRefl {n}


> transitiveLTE : (m : Nat) -> (n : Nat) -> (o : Nat) ->
>                 LTE m n -> LTE n o -> LTE m o
> transitiveLTE  Z       n     o   LTEZero                 nlteo  = LTEZero
> transitiveLTE (S m) (S n) (S o) (LTESucc mlten) (LTESucc nlteo) = LTESucc (transitiveLTE m n o mlten nlteo)


> totalLTE : (m : Nat) -> (n : Nat) -> Either (LTE m n) (LTE n m)
> totalLTE  Z    n     = Left LTEZero
> totalLTE (S m) Z     = Right LTEZero
> totalLTE (S m) (S n) with (totalLTE m n)
>   | (Left  p) = Left  (LTESucc p)
>   | (Right p) = Right (LTESucc p)



> preorderNatLTE : Preorder Nat
> preorderNatLTE =
>   MkPreorder LTE reflexiveLTE transitiveLTE


> totalPreorderNatLTE : TotalPreorder Nat
> totalPreorderNatLTE =
>   MkTotalPreorder LTE reflexiveLTE transitiveLTE totalLTE


Properties of |plus|:

> {- Not used

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

> plusPlusElimRight : {m1, n1, m2, n2 : Nat} -> m1 + n1 = m2 + n2 -> n1 = n2 -> m1 = m2

> plusElimLeft : (m1 : Nat) -> (n : Nat) -> (m2 : Nat) -> m1 + n = m2 -> m1 = m2 -> n = Z
> plusElimLeft m n m p Refl = plusLeftLeftRightZero m n p

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


> |||
> minusLemma2 : LTE m n -> n - m = S l -> LTE (S m) n
> minusLemma2 {m = Z}    {n = Z}    p q = absurd q
> minusLemma2 {m = Z}    {n = S n'} p q = LTESucc LTEZero
> minusLemma2 {m = S m'} {n = Z}    p q = absurd p
> minusLemma2 {m = S m'} {n = S n'} (LTESucc p') q = LTESucc (minusLemma2 p' q)


> |||
> minusLemma3 : LTE m n -> Z = n - m -> m = n
> minusLemma3 {m = Z}    {n = Z}    p q = Refl
> minusLemma3 {m = Z}    {n = S n'} p q = absurd q
> minusLemma3 {m = S m'} {n = Z}    p q = absurd p
> minusLemma3 {m = S m'} {n = S n'} (LTESucc p') q =
>   eqSucc m' n' (minusLemma3 {m = m'} {n = n'} p' q') where
>     q' : Z = n' - m'
>     q' = trans q Refl


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


Properties of |plus| and |minus|:

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


Properties of |mult|

> multSuccNotZero : (m : Nat) -> (n : Nat) -> Not ((S m) * (S n) = Z)
> multSuccNotZero m  n  p = absurd p  

> multNotZeroNotZero : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Not (n = Z) -> Not (m * n = Z)
> multNotZeroNotZero  Z     n    p q = void (p Refl)
> multNotZeroNotZero (S m)  Z    p q = void (q Refl)
> multNotZeroNotZero (S m) (S n) p q = multSuccNotZero m n

> multNotZeroNotZeroLeft : (m : Nat) -> (n : Nat) -> Not (m * n = Z) -> Not (m = Z)
> multNotZeroNotZeroLeft  Z     n    p = void (p (multZeroLeftZero n))
> multNotZeroNotZeroLeft (S m)  _    _ = SIsNotZ

> multNotZeroNotZeroRight : (m : Nat) -> (n : Nat) -> Not (m * n = Z) -> Not (n = Z)
> multNotZeroNotZeroRight m  Z     p = void (p (multZeroRightZero m))
> multNotZeroNotZeroRight _ (S n)  _ = SIsNotZ

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


> ||| LT is decidable
> decLT : (m : Nat) -> (n : Nat) -> Dec (LT m n)
> decLT m n = decLTE (S m) n


Uniqueness

> ||| LTE is unique
> uniqueLTE : (p1 : LTE m n) -> (p2 : LTE m n) -> p1 = p2
> uniqueLTE  LTEZero     LTEZero    = Refl
> uniqueLTE  LTEZero    (LTESucc p) impossible
> uniqueLTE (LTESucc p)  LTEZero    impossible
> uniqueLTE (LTESucc p) (LTESucc q) = cong (uniqueLTE p q)

> ||| LT is unique
> uniqueLT : (p1 : LT m n) -> (p2 : LT m n) -> p1 = p2
> uniqueLT {m} {n} = uniqueLTE {m = S m} {n = n}


Divisor properties:

> divByLemma : (d : Nat) -> (m : Nat) -> (dDm : d `Divisor` m) -> d * (divBy d m dDm) = m
> divByLemma d m (mkDivisor d m (Evidence q prf)) = prf

> anyDivisorZ : (m : Nat) -> m `Divisor` Z
> anyDivisorZ m = mkDivisor m Z (Evidence Z (multZeroRightZero m))

> oneDivisorAny : (m : Nat) -> (S Z) `Divisor` m
> oneDivisorAny m = mkDivisor (S Z) m (Evidence m (multOneLeftNeutral m))

> anyDivisorAny : (m : Nat) -> m `Divisor` m
> anyDivisorAny m = mkDivisor m m (Evidence (S Z) (multOneRightNeutral m))

> divisorPlusLemma1 : (m : Nat) -> (n : Nat) -> (d : Nat) ->
>                      d `Divisor` m -> d `Divisor` n -> d `Divisor` (n + m)
> divisorPlusLemma1 m n d (mkDivisor d m (Evidence q1 p1)) (mkDivisor d n (Evidence q2 p2)) = 
>   mkDivisor d (n + m) (Evidence (q1 + q2) p) where
>     s1 : d * (q1 + q2) = d * q1 + d * q2
>     s1 = multDistributesOverPlusRight d q1 q2
>     s2 : d * (q1 + q2) = m + d * q2
>     s2 = replace {x = d * q1} {y = m} {P = \ ZUZU => d * (q1 + q2) = ZUZU + d * q2} p1 s1
>     s3 : d * (q1 + q2) = m + n
>     s3 = replace {x = d * q2} {y = n} {P = \ ZUZU => d * (q1 + q2) = m + ZUZU} p2 s2
>     p  : d * (q1 + q2) = n + m
>     p  = replace {x = m + n} {y = n + m} {P = \ ZUZU => d * (q1 + q2) = ZUZU} (plusCommutative m n) s3

> divisorPlusLemma2 : (m : Nat) -> (n : Nat) -> (d : Nat) ->
>                     d `Divisor` m -> d `Divisor` n -> d `Divisor` (m + n)
> divisorPlusLemma2 m n d (mkDivisor d m (Evidence q1 p1)) (mkDivisor d n (Evidence q2 p2)) =
>   mkDivisor d (m + n) (Evidence (q1 + q2) p) where
>     s1 : d * (q1 + q2) = d * q1 + d * q2
>     s1 = multDistributesOverPlusRight d q1 q2
>     s2 : d * (q1 + q2) = m + d * q2
>     s2 = replace {x = d * q1} {y = m} {P = \ ZUZU => d * (q1 + q2) = ZUZU + d * q2} p1 s1
>     p : d * (q1 + q2) = m + n
>     p = replace {x = d * q2} {y = n} {P = \ ZUZU => d * (q1 + q2) = m + ZUZU} p2 s2

> ||| If a number divides two numbers, it also divides their difference
> divisorMinusLemma : (m : Nat) -> (n : Nat) -> (d : Nat) ->
>                     d `Divisor` m -> d `Divisor` n -> d `Divisor` (n - m)
> divisorMinusLemma m n d (mkDivisor d m (Evidence q1 p1)) (mkDivisor d n (Evidence q2 p2)) = 
>   mkDivisor d (n - m) (Evidence q p) where
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

> divisorOneLemma : (d : Nat) -> (d' : Nat) -> (S d) * d' `Divisor` (S d) -> d' `Divisor` S Z
> divisorOneLemma d d' (mkDivisor ((S d) * d') (S d) (Evidence q p)) =
>   mkDivisor d' (S Z) (Evidence q p') where
>     s1 : ((S d) * d') * q = S d
>     s1 = p
>     s2 : (S d) * (d' * q) = S d
>     s2 = replace {x = ((S d) * d') * q} {y = (S d) * (d' * q)} {P = \ ZUZU => ZUZU = S d} (sym (multAssociative (S d) d' q)) s1
>     p' : d' * q = S Z
>     p' = multElim1 d (d' * q) s2

> divisorOneLemma' : (d : Nat) -> (d' : Nat) -> Not (d = Z) -> d * d' `Divisor` d -> d' `Divisor` S Z
> divisorOneLemma'  Z    _  dNotZ _  = void (dNotZ Refl)
> divisorOneLemma' (S d) d' dNotZ (mkDivisor ((S d) * d') (S d) (Evidence q p)) =
>   mkDivisor d' (S Z) (Evidence q p') where
>     s1 : ((S d) * d') * q = S d
>     s1 = p
>     s2 : (S d) * (d' * q) = S d
>     s2 = replace {x = ((S d) * d') * q} {y = (S d) * (d' * q)} {P = \ ZUZU => ZUZU = S d} (sym (multAssociative (S d) d' q)) s1
>     p' : d' * q = S Z
>     p' = multElim1 d (d' * q) s2

> ||| 
> divisorTowerLemma: (d : Nat) -> (d' : Nat) -> (m : Nat) -> 
>                    (dDm : d `Divisor` m) -> d' `Divisor` (divBy d m dDm) -> d * d' `Divisor` m
> divisorTowerLemma d d' m dDm d'DmOd = mkDivisor (d * d') m (Evidence q' p) where
>   q' : Nat
>   q' = divBy d' (divBy d m dDm) d'DmOd
>   s1 : d' * q' = divBy d m dDm
>   s1 = divByLemma d' (divBy d m dDm) d'DmOd
>   s2 : d * (divBy d m dDm) = m
>   s2 = divByLemma d m dDm
>   s3 : d * (d' * q') = m
>   s3 = replace {x = divBy d m dDm} {y = d' * q'} {P = \ ZUZU => d * ZUZU = m} (sym s1) s2
>   p : (d * d') * q' = m
>   p = replace {x = d * (d' * q')} {y = (d * d') * q'} {P = \ ZUZU => ZUZU = m} (multAssociative d d' q') s3


Greatest common divisor properties:

> gcdLemma : (v : GCD (S d) m n) -> 
>            d' `Divisor` (divBy (S d) m (gcdDivisorFst v)) -> d' `Divisor` (divBy (S d) n (gcdDivisorSnd v)) -> 
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

> gcdLemma' : (v : GCD d m n) -> Not (d = Z) ->
>             d' `Divisor` (divBy d m (gcdDivisorFst v)) -> d' `Divisor` (divBy d n (gcdDivisorSnd v)) -> 
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

Coprime properties:

> ||| Coprime is symmetric
> symmetricCoprime : Coprime m n -> Coprime n m
> symmetricCoprime {m} {n} (mkCoprime (mkGCD {d} {m} {n} dDm dDn dG) dEQone) = 
>   (mkCoprime (mkGCD dDn dDm dG') dEQone) where
>     dG' : (d' : Nat) -> Divisor d' n -> Divisor d' m -> Divisor d' d
>     dG' d' d'Dn d'Dm = dG d' d'Dm d'Dn

> ||| Any number is coprime with one
> anyCoprimeOne : Coprime m (S Z)
> anyCoprimeOne {m} = mkCoprime (mkGCD oDm oDo oG) Refl where
>   oDm : (S Z) `Divisor` m
>   oDm = oneDivisorAny m
>   oDo : (S Z) `Divisor` (S Z)
>   oDo = anyDivisorAny (S Z)
>   oG  : (d : Nat) -> d `Divisor` m -> d `Divisor` (S Z) -> d `Divisor` (S Z)
>   oG d dDm dDo = dDo 

> ||| Division by gcd yields coprime numbers
> gcdCoprimeLemma : (v : GCD (S d) m n) -> Coprime (divBy (S d) m (gcdDivisorFst v)) (divBy (S d) n (gcdDivisorSnd v))
> gcdCoprimeLemma {d} {m} {n} v = mkCoprime (mkGCD d'Dm' d'Dn' d'G) Refl where
>   dDm     : (S d) `Divisor` m
>   dDm     = gcdDivisorFst v
>   dDn     : (S d) `Divisor` n
>   dDn     = gcdDivisorSnd v
>   m'      : Nat
>   m'      = divBy (S d) m dDm
>   n'      : Nat
>   n'      = divBy (S d) n dDn
>   d'Dm'   : S Z `Divisor` m'
>   d'Dm'   = oneDivisorAny m'
>   d'Dn'   : S Z `Divisor` n'
>   d'Dn'   = oneDivisorAny n'
>   d'G     : (d'' : Nat) -> d'' `Divisor` m' -> d'' `Divisor` n' -> d'' `Divisor` (S Z)
>   d'G d'' = gcdLemma v

> ||| Division by gcd yields coprime numbers
> gcdCoprimeLemma' : (v : GCD d m n) -> Not (d = Z) -> Coprime (divBy d m (gcdDivisorFst v)) (divBy d n (gcdDivisorSnd v))
> gcdCoprimeLemma' {d} {m} {n} v dNotZ = mkCoprime (mkGCD d'Dm' d'Dn' d'G) Refl where
>   dDm     : d `Divisor` m
>   dDm     = gcdDivisorFst v
>   dDn     : d `Divisor` n
>   dDn     = gcdDivisorSnd v
>   m'      : Nat
>   m'      = divBy d m dDm
>   n'      : Nat
>   n'      = divBy d n dDn
>   d'Dm'   : S Z `Divisor` m'
>   d'Dm'   = oneDivisorAny m'
>   d'Dn'   : S Z `Divisor` n'
>   d'Dn'   = oneDivisorAny n'
>   d'G     : (d'' : Nat) -> d'' `Divisor` m' -> d'' `Divisor` n' -> d'' `Divisor` (S Z)
>   d'G d'' = gcdLemma' v dNotZ
