> module NatLTEProperties

> %default total
> %access public export
> %auto_implicits on


LTE is unique:

> ||| LTE is unique
> uniqueLTE : (p1 : LTE m n) -> (p2 : LTE m n) -> p1 = p2
> uniqueLTE  LTEZero     LTEZero    = Refl
> uniqueLTE  LTEZero    (LTESucc p) impossible
> uniqueLTE (LTESucc p)  LTEZero    impossible
> uniqueLTE (LTESucc p) (LTESucc q) = cong (uniqueLTE p q)
> %freeze uniqueLTE


LTE is decidable:

> ||| LTE is decidable
> decLTE : (m : Nat) -> (n : Nat) -> Dec (LTE m n)
> --decLTE = lte
> --{-
> decLTE Z _     = Yes LTEZero
> decLTE (S m) Z = No succNotLTEzero
> decLTE (S m) (S n) with (decLTE m n)
>   | (Yes p) = Yes (LTESucc p)
>   | (No contra) = No (\ p => contra (fromLteSucc p))
> ---}
> %freeze decLTE


|LTE| is a total preorder:

> ||| LTE is reflexive
> reflexiveLTE : (n : Nat) -> LTE n n
> reflexiveLTE n = lteRefl {n}
> %freeze reflexiveLTE

> ||| LTE is transitive
> transitiveLTE : (m : Nat) -> (n : Nat) -> (o : Nat) ->
>                 LTE m n -> LTE n o -> LTE m o
> transitiveLTE  Z       n     o   LTEZero                 nlteo  = LTEZero
> transitiveLTE (S m) (S n) (S o) (LTESucc mlten) (LTESucc nlteo) = LTESucc (transitiveLTE m n o mlten nlteo)
> %freeze transitiveLTE

> ||| LTE is total
> totalLTE : (m : Nat) -> (n : Nat) -> Either (LTE m n) (LTE n m)
> totalLTE  Z    n     = Left LTEZero
> totalLTE (S m) Z     = Right LTEZero
> totalLTE (S m) (S n) with (totalLTE m n)
>   | (Left  p) = Left  (LTESucc p)
>   | (Right p) = Right (LTESucc p)
> %freeze totalLTE


Properties of |LTE| and successor:

> |||
> notLTELemma0 : Not (S m `LTE` S n) -> Not (m `LTE` n)
> notLTELemma0 contra = contra . LTESucc
> %freeze notLTELemma0

> |||
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
> idSuccPreservesLTE : (m : Nat) -> (n : Nat) -> m `LTE` n -> m `LTE` (S n)
> idSuccPreservesLTE  Z     n    prf = LTEZero
> idSuccPreservesLTE (S m)  Z    prf = absurd prf
> idSuccPreservesLTE (S m) (S n) prf = LTESucc (idSuccPreservesLTE m n (fromLteSucc prf))
> %freeze idSuccPreservesLTE


Properties of |LTE| and |plus|:

> |||
> elimSuccRightLTEPlus : {a, b, c, d : Nat} -> LTE (a + S b) (c + S d) -> LTE (a + b) (c + d)
> elimSuccRightLTEPlus {a} {b} {c} {d} aSbLTEcSd = s6 where
>   s0 : LTE (a + S b) (c + S d)
>   s0 = aSbLTEcSd
>   s1 : LTE (S b + a) (c + S d)
>   s1 = replace {P = \ ZUZU => LTE ZUZU (c + S d)} (plusCommutative a (S b)) s0
>   s2 : LTE (S b + a) (S d + c)
>   s2 = replace {P = \ ZUZU => LTE (S b + a) ZUZU } (plusCommutative c (S d)) s1
>   s3 : LTE (S (b + a)) (S (d + c))
>   s3 = s2
>   s4 : LTE (b + a) (d + c)
>   s4 = fromLteSucc s3
>   s5 : LTE (a + b) (d + c)
>   s5 = replace {P = \ ZUZU => LTE ZUZU (d + c)} (plusCommutative b a) s4
>   s6 : LTE (a + b) (c + d)
>   s6 = replace {P = \ ZUZU => LTE (a + b) ZUZU}(plusCommutative d c) s5
> %freeze elimSuccRightLTEPlus

> |||
> idAnyPlusPreservsLTE : {a, b, c : Nat} -> LTE a b -> LTE a (c + b)
> idAnyPlusPreservsLTE {a} {b} {c = Z}   aLTEb = aLTEb
> idAnyPlusPreservsLTE {a} {b} {c = S m} aLTEb = idSuccPreservesLTE a (m + b) (idAnyPlusPreservsLTE {a = a} {b = b} {c = m} aLTEb)  

> |||
> monotoneNatPlusLTE : {a, b, c, d  : Nat} ->
>                      LTE a b -> LTE c d -> LTE (a + c) (b + d)
> monotoneNatPlusLTE {a = Z}   {b = Z}   {c} {d} _           cLTEd = 
>   cLTEd
> monotoneNatPlusLTE {a = Z}   {b = S n} {c} {d} _           cLTEd = 
>   idAnyPlusPreservsLTE {a = c} {b = d} {c = S n} cLTEd
> monotoneNatPlusLTE {a = S m} {b = Z}   {c} {d} aLTEb       _     = 
>   absurd aLTEb
> monotoneNatPlusLTE {a = S m} {b = S n} {c} {d} (LTESucc p) cLTEd = 
>   LTESucc (monotoneNatPlusLTE {a = m} {b = n} {c = c} {d = d} p cLTEd)
> %freeze monotoneNatPlusLTE

> |||
> elimRightPlusLTE : {a, b, c, d : Nat} ->
>                    LTE (a + c) (b + d) -> c = d -> LTE a b
> elimRightPlusLTE {a} {b} {c = Z} {d = Z} acLTEbd _ = s2 where
>   s1 : LTE a (b + Z)
>   s1 = replace {P = \ ZUZ => LTE ZUZ (b + Z)} (plusZeroRightNeutral a) acLTEbd
>   s2 : LTE a b
>   s2 = replace {P = \ ZUZ => LTE a ZUZ} (plusZeroRightNeutral b) s1
> elimRightPlusLTE {a} {b} {c = Z} {d = S n} _ ZEQSn = absurd ZEQSn
> elimRightPlusLTE {a} {b} {c = S m} {d = Z} _ SmEQZ = void (SIsNotZ SmEQZ)
> elimRightPlusLTE {a} {b} {c = S m} {d = S n} aSmLTEbSn SmEQSn = s4 where
>   s1 : LTE (a + S m) (b + S n)
>   s1 = aSmLTEbSn
>   s2 : LTE (a + m) (b + n)
>   s2 = elimSuccRightLTEPlus s1
>   s3 : m = n
>   s3 = succInjective m n SmEQSn
>   s4 : LTE a b
>   s4 = elimRightPlusLTE {a = a} {b = b} {c = m} {d = n} s2 s3
> %freeze elimRightPlusLTE


Properties of |LTE| and |mult|:

> |||
> monotoneNatMultLTE : {a, b, c, d  : Nat} ->
>                      LTE a b -> LTE c d -> LTE (a * c) (b * d)
> monotoneNatMultLTE {a = Z}   {b}       {c} {d} _ _ = LTEZero
> monotoneNatMultLTE {a = S m} {b = Z}   {c} {d} aLTEb _ = absurd aLTEb
> monotoneNatMultLTE {a = S m} {b = S n} {c} {d} (LTESucc mLTEn) cLTEd = s3 where
>   s1 : LTE (c + m * c) (d + n * d)
>   s1 = monotoneNatPlusLTE {a = c} {b = d} {c = m * c} {d = n * d} 
>        cLTEd (monotoneNatMultLTE {a = m} {b = n} {c = c} {d = d} mLTEn cLTEd)
>   s2 : LTE ((S m) * c) (d + n * d)
>   s2 = replace {P = \ ZUZ => LTE ZUZ (d + n * d)} Refl s1
>   s3 : LTE ((S m) * c) ((S n) * d)
>   s3 = replace {P = \ ZUZ => LTE ((S m) * c) ZUZ} Refl s2
> %freeze monotoneNatMultLTE

> |||
> elimRightMultLTE : {a, b, c, d : Nat} ->
>                    LTE (a * c) (b * d) -> c = d -> Not (c = Z) -> LTE a b
> elimRightMultLTE {a = Z}   {b}       {c}       {d} _       _    _      = LTEZero
> elimRightMultLTE {a = S m} {b = Z}   {c = Z}   {d} _       _    contra = void (contra Refl)
> elimRightMultLTE {a = S m} {b = Z}   {c = S n} {d} acLTEbd _    _      = absurd acLTEbd
> elimRightMultLTE {a = S m} {b = S n} {c}       {d} acLTEbd cEQd ncEQZ  = s6 where
>   s1 : LTE (c + m * c) (d + n * d)
>   s1 = acLTEbd
>   s2 : LTE (m * c + c) (d + n * d)
>   s2 = replace {P = \ ZUZ => LTE ZUZ (d + n * d)} (plusCommutative c (m * c)) s1 
>   s3 : LTE (m * c + c) (n * d + d)
>   s3 = replace {P = \ ZUZ => LTE (m * c + c) ZUZ} (plusCommutative d (n * d)) s2 
>   s4 : LTE (m * c) (n * d)
>   s4 = elimRightPlusLTE s3 cEQd
>   s5 : LTE m n
>   s5 = elimRightMultLTE s4 cEQd ncEQZ
>   s6 : LTE (S m) (S n)
>   s6 = LTESucc s5
> %freeze elimRightMultLTE


> {-

> ---}
