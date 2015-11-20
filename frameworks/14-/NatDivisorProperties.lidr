> module NatDivisorProperties

> import Syntax.PreorderReasoning

> import Basics
> import NatOperations
> import NatProperties
> import NatDivisor
> import NatDivisorOperations


%default total


> ||| Fundamental quotient lemma
> quotientLemma : (m : Nat) -> (d : Nat) -> (dDm : d `Divisor` m) -> d * (quotient m d dDm) = m
> quotientLemma m d (Evidence q prf) = prf
> %freeze quotientLemma


Properties of |Divisor|:

> ||| Any natural number is a divisor of zero
> anyDivisorZ : (m : Nat) -> m `Divisor` Z
> anyDivisorZ m = Evidence Z (multZeroRightZero m)
> %freeze anyDivisorZ

> ||| One is a divisor of any natural number
> oneDivisorAny : (m : Nat) -> (S Z) `Divisor` m
> oneDivisorAny m = Evidence m (multOneLeftNeutral m)
> %freeze oneDivisorAny

> ||| Any natural number is a divisor of itself
> anyDivisorAny : (m : Nat) -> m `Divisor` m
> anyDivisorAny m = Evidence (S Z) (multOneRightNeutral m)
> %freeze anyDivisorAny

> ||| |Divisor| is reflexive
> divisorReflexive : (m : Nat) -> m `Divisor` m
> divisorReflexive = anyDivisorAny
> %freeze divisorReflexive

> ||| |Divisor| is transitive
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

> ||| |Divisor| is antysymmetric
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

> ||| Any divisor of two numbers is a divisor of their sum
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

> ||| Any divisor of two numbers is a divisor of their sum
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

> ||| The product of (two) divisors (of two natural numbers) is a divisor of the
> ||| product (of those numbers)
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

> ||| Any divisor of two numbers is a divisor of their difference
> divisorMinusLemma : (m : Nat) -> (n : Nat) -> (d : Nat) ->
>                     d `Divisor` m -> d `Divisor` n -> d `Divisor` (n - m)
> divisorMinusLemma m n d (Evidence q1 p1) (Evidence q2 p2) =
>   Evidence q p where
>     q : Nat
>     q = q2 - q1
>     p : d * q = n - m
>     p = s2 where
>       s1 : d * q2 - d * q1 = n - m
>       s1 = cong2 p2 p1
>       s2 : d * (q2 - q1) = n - m
>       s2 = replace {x = d * q2 - d * q1}
>                    {y = d * (q2 - q1)}
>                    {P = \ZUZU => ZUZU = n - m}
>                    (sym (multDistributesOverMinusRight d q2 q1))
>                    s1
> %freeze divisorMinusLemma

> ||| 
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

> |||
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
> divisorOneLemma'' : (d : Nat) -> (d' : Nat) -> Z `LT` d -> d * d' `Divisor` d -> d' `Divisor` S Z
> divisorOneLemma''  Z    _  p  _             = 
>   absurd p
> divisorOneLemma'' (S d) d' _ (Evidence q p) =
>   Evidence q p' where
>     s1 : ((S d) * d') * q = S d
>     s1 = p
>     s2 : (S d) * (d' * q) = S d
>     s2 = replace {x = ((S d) * d') * q} {y = (S d) * (d' * q)} {P = \ ZUZU => ZUZU = S d} (sym (multAssociative (S d) d' q)) s1
>     p' : d' * q = S Z
>     p' = multElim1 d (d' * q) s2
> %freeze divisorOneLemma''

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


Properties of |quotient|:

> |||
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

> |||
> quotientDivisorLemma2 : (m : Nat) -> 
>                         (d1 : Nat) -> (d1Dm : d1 `Divisor` m) ->
>                         (d2 : Nat) -> (d2Dm : d2 `Divisor` m) -> 
>                         d1 = d2 -> Not (d1 = Z) -> quotient m d1 d1Dm = quotient m d2 d2Dm 
> quotientDivisorLemma2 m d (Evidence q1 dq1EQm) d (Evidence q2 dq2EQm) Refl NdEQZ =
>     ( quotient m d (Evidence q1 dq1EQm) )
>   ={ Refl }=
>     ( q1 )
>   ={ multMultElimLeft d d q1 q2 Refl NdEQZ (trans dq1EQm (sym dq2EQm)) }=
>     ( q2 )
>   ={ Refl }=
>     ( quotient m d (Evidence q2 dq2EQm) )
>   QED
> %freeze quotientDivisorLemma2

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


> quotientScaleInvariant : (m : Nat) -> (n : Nat) -> (d : Nat) -> Not (d * n = Z) ->
>                          (nDm : n `Divisor` m) -> (dnDdm : (d * n) `Divisor` (d * m)) ->
>                          quotient m n nDm = quotient (d * m) (d * n) dnDdm 
> quotientScaleInvariant m n d ndnEQZ (Evidence p npEQm) (Evidence q dnqEQdm) =
>   let s1 : (d * (n * p) = d * m)
>          = multPreservesEq d d (n * p) m Refl npEQm in
>   let s2 : ((d * n) * p = d * m)
>          = replace {P = \ ZUZU => ZUZU = d * m} (multAssociative d n p) s1 in
>   let s3 : ((d * n) * p = (d * n) * q)
>          = trans s2 (sym dnqEQdm) in
>     ( quotient m n (Evidence p npEQm) )
>   ={ Refl }=
>     ( p )
>   ={ multMultElimLeft (d * n) (d * n) p q Refl ndnEQZ s3 }=
>     ( q )
>   ={ Refl }=
>     ( quotient (d * m) (d * n) (Evidence q dnqEQdm) )
>   QED
>        
   
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

>  flipQuotientLemma : (m : Nat) -> (n : Nat) -> (d : Nat) ->
>                      (dDm : d `Divisor` m) -> (dDn : d `Divisor` n) ->
>                      (quotient m d dDm) * n = m * (quotient n d dDn)
>  flipQuotientLemma m n d dDm dDn = 
>    let qmd = quotient m d dDm in
>    let qnd = quotient n d dDn in
>      ( qmd * n )
>    ={ cong {f = \ ZUZU => qmd * ZUZU} (sym (quotientLemma n d dDn)) }=
>      ( qmd * (d * qnd) )
>    ={ multAssociative qmd d qnd }=
>      ( (qmd * d) * qnd )
>    ={ cong {f = \ ZUZU => ZUZU * qnd} (multCommutative qmd d) }=
>      ( (d * qmd) * qnd )
>    ={ cong {f = \ ZUZU => ZUZU * qnd} (quotientLemma m d dDm) }=
>      ( m * qnd )
>    QED

> quotientEqLemma : (m1 : Nat) -> (d1 : Nat) -> (d1Dm1 : d1 `Divisor` m1) ->
>                   (m2 : Nat) -> (d2 : Nat) -> (d2Dm2 : d2 `Divisor` m2) ->
>                   m1 = m2 -> d1 = d2 -> Not (d1 = Z) ->
>                   quotient m1 d1 d1Dm1 = quotient m2 d2 d2Dm2
> quotientEqLemma m d (Evidence p dpEQm) m d (Evidence q dqEQm) Refl Refl ndEQZ =
>     ( quotient m d (Evidence p dpEQm) )
>   ={ Refl }=
>     ( p )
>   ={ multMultElimLeft d d p q Refl ndEQZ (trans dpEQm (sym dqEQm)) }=
>     ( q )
>   ={ Refl }=
>     ( quotient m d (Evidence q dqEQm) )
>   QED


> {-

> ---}
