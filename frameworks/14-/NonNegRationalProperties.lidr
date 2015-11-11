> module NonNegRationalProperties


> import Syntax.PreorderReasoning

> import NonNegRational
> import NonNegRationalOperations
> import NatGCD
> import NatGCDOperations
> import NatGCDProperties
> import NatGCDEuclid
> import NatProperties
> import EqualityProperties
> import Fraction
> import NatCoprime
> import NatCoprimeProperties
> import Basics


> %default total


> ||| Non-negative rationals are in |Show|
> instance Show NonNegQ where
>   show q = show (num q) ++ "/" ++ show (den q)

> ||| Non-negative rationals are in |Num|
> instance Num NonNegQ where
>   (+) = plus
>   (*) = mult
>   fromInteger = NonNegRationalOperations.fromNat . fromIntegerNat


Propertie of NonNegQ:

> |||
> lemma : (n1 : Nat) -> (d1 : Nat) -> (zLTd1 : Z `LT` d1) -> (gcdOne1 : gcd (alg n1 d1) = S Z) -> 
>         (n2 : Nat) -> (d2 : Nat) -> (zLTd2 : Z `LT` d2) -> (gcdOne2 : gcd (alg n2 d2) = S Z) -> 
>         n1 = n2 -> d1 = d2 ->
>         MkNonNegQ n1 d1 zLTd1 gcdOne1 = MkNonNegQ n2 d2 zLTd2 gcdOne2
> lemma n d zLTd1 gcdOne1 n d zLTd2 gcdOne2 Refl Refl =
>     ( MkNonNegQ n d zLTd1 gcdOne1 )
>   ={ replace {x = zLTd1} 
>              {y = zLTd2} 
>              {P = \ ZUZU => MkNonNegQ n d zLTd1 gcdOne1 = MkNonNegQ n d ZUZU gcdOne1} 
>              (uniqueLT zLTd1 zLTd2) Refl }=
>     ( MkNonNegQ n d zLTd2 gcdOne1 )
>   ={ replace {x = gcdOne1} 
>              {y = gcdOne2} 
>              {P = \ ZUZU => MkNonNegQ n d zLTd2 gcdOne1 = MkNonNegQ n d zLTd2 ZUZU} 
>              ((uniqueEq (gcd (alg n d)) (S Z)) gcdOne1 gcdOne2) Refl }=
>     ( MkNonNegQ n d zLTd2 gcdOne2 )
>   QED


Properties of |num|, |den|:

> -- denPreservesEquality : (q1 : NonNegQ) -> (q2 : NonNegQ) -> q1 = q2 -> den q1 = den q2
> -- denPreservesEquality (MkNonNegQ n d p q) (MkNonNegQ n d p q) Refl = Refl

> ||| The numerator of zero is zero
> numZeroZero : NonNegRationalOperations.num (fromInteger 0) = Z
> numZeroZero = ( NonNegRationalOperations.num (fromInteger 0) )
>             ={ Refl }=
>               ( NonNegRationalOperations.num (fromNat (fromIntegerNat 0)) )
>             ={ Refl }=
>               ( NonNegRationalOperations.num (fromNat Z) )
>             ={ Refl }=
>               ( NonNegRationalOperations.num (MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z)) )
>             ={ Refl }=
>               ( Z )
>             QED
> %freeze numZeroZero


Properties of fromFraction:

> ||| 
> fromFractionLemma : (x : Fraction) -> 
>                     (zLTdx : Z `LT` den x) ->
>                     (gcdOne : gcd (alg (num x) (den x)) = S Z) ->
>                     fromFraction x zLTdx = MkNonNegQ (num x) (den x) zLTdx gcdOne
> fromFractionLemma x zLTdx gcdOne =
>   let x'      : Fraction      
>               = reduce alg x in
>   let zLTdx'  : (Z `LT` den x')
>               = reducePreservesPositivity alg x zLTdx in
>   let cnx'dx' : (Coprime (num x') (den x')) 
>               = reduceYieldsCoprimes alg x zLTdx in
>   let gcdOne' : (gcd (alg (num x') (den x')) = S Z) 
>               = gcdOneCoprimeLemma2 (num x') (den x') alg cnx'dx' in
>   let x'EQx   : (x' = x)         
>               = reducePreservesCoprimes alg x (gcdOneCoprimeLemma1 alg (num x) (den x) gcdOne) in
>   let n'EQn   : (num x' = num x) 
>               = cong x'EQx in
>   let d'EQd   : (den x' = den x) 
>               = cong x'EQx in
>     ( fromFraction x zLTdx )
>   ={ Refl }=
>     ( MkNonNegQ (num x') (den x') zLTdx' gcdOne' )
>   ={ lemma (num x') (den x') zLTdx' gcdOne' (num x) (den x) zLTdx gcdOne n'EQn d'EQd }=
>     ( MkNonNegQ (num x) (den x) zLTdx gcdOne )
>   QED


> |||
> fromFractionToFractionLemma : 
>   (q : NonNegQ) -> 
>   fromFraction (toFraction q) (toFractionPreservesDenominatorPositivity q) = q
> fromFractionToFractionLemma (MkNonNegQ n d zLTd gcdOne) =
>   let zLTd' = toFractionPreservesDenominatorPositivity (MkNonNegQ n d zLTd gcdOne) in
>     ( fromFraction (toFraction (MkNonNegQ n d zLTd gcdOne)) zLTd' )
>   ={ Refl }=
>     ( fromFraction (n, d) zLTd )
>   ={ fromFractionLemma (n, d) zLTd gcdOne }=
>     ( (MkNonNegQ n d zLTd gcdOne) )
>   QED
> %freeze fromFractionToFractionLemma


> ||| fromFraction preserves identity
> fromFractionLemma2 : 
>   (x : Fraction) -> 
>   (zLTdx : Z `LT` den x) ->
>   (y : Fraction) -> 
>   (zLTdy : Z `LT` den y) ->
>   x = y -> 
>   fromFraction x zLTdx = fromFraction y zLTdy
> fromFractionLemma2 x zLTdx y zLTdy xEQy =
>     ( fromFraction x zLTdx )
>   ={ depCong2' {alpha = Fraction}
>                {P = \ ZUZU => Z `LT` (den ZUZU)}
>                {Q = \ ZUZU => \ zLTdenZUZU => NonNegQ}
>                {a1 = x}
>                {a2 = y}
>                {Pa1 = zLTdx}
>                {Pa2 = zLTdy}
>                (\ ZUZU => \ zLTdenZUZU => fromFraction ZUZU zLTdenZUZU)
>                xEQy (uniqueLT' Refl (denPreservesEquality x y xEQy) zLTdx zLTdy) }=
>     ( fromFraction y zLTdy )
>   QED
> %freeze fromFractionLemma2


> ||| fromFraction is "linear"
> fromFractionLinear : 
>   (x : Fraction) -> 
>   (zLTdx : Z `LT` den x) ->
>   (y : Fraction) -> 
>   (zLTdy : Z `LT` den y) ->
>   fromFraction (x + y) (plusPreservesPositivity x y zLTdx zLTdy)
>   =
>   fromFraction x zLTdx + fromFraction y zLTdy
> fromFractionLinear x zLTdx y zLTdy =
>   let x'             :  Fraction
>                      =  reduce alg x in
>   let nx'            :  Nat
>                      =  num x' in
>   let dx'            :  Nat
>                      =  den x' in
>   let y'             :  Fraction
>                      =  reduce alg y in
>   let ny'            :  Nat
>                      =  num y' in
>   let dy'            :  Nat
>                      =  den y' in
>   let zLTdx'         :  (Z `LT` dx')
>                      =  reducePreservesPositivity alg x zLTdx in
>   let nx'dx'coprime  :  (Coprime nx' dx')
>                      =  reduceYieldsCoprimes alg x zLTdx in
>   let nx'dx'gcd1     :  (gcd (alg nx' dx') = S Z)
>                      =  (gcdOneCoprimeLemma2 nx' dx' alg nx'dx'coprime) in
>   let zLTdy'         :  (Z `LT` dy')
>                      =  reducePreservesPositivity alg y zLTdy in
>   let ny'dy'coprime  :  (Coprime ny' dy')
>                      =  reduceYieldsCoprimes alg y zLTdy in
>   let ny'dy'gcd1     :  (gcd (alg ny' dy') = S Z)
>                      =  (gcdOneCoprimeLemma2 ny' dy' alg ny'dy'coprime) in
>   let qx'            :  NonNegQ
>                      =  MkNonNegQ nx' dx' zLTdx' nx'dx'gcd1 in
>   let qy'            :  NonNegQ
>                      =  MkNonNegQ ny' dy' zLTdy' ny'dy'gcd1 in
>   let zLTdqx'        :  (Z `LT` den qx')
>                      =  toFractionPreservesDenominatorPositivity qx' in
>   let zLTdqy'        :  (Z `LT` den qy')
>                      =  toFractionPreservesDenominatorPositivity qy' in
>   let fqx'           :  Fraction
>                      =  toFraction qx' in
>   let fqy'           :  Fraction
>                      =  toFraction qy' in
>   let zLTdfqx'fqy'   :  (Z `LT` den (fqx' + fqy'))
>                      =  plusPreservesPositivity fqx' fqy' zLTdqx' zLTdqy' in
> {-
>   let z              :  Fraction
>                      =  x + y in
>   let zLTdz          :  (Z `LT` den z)
>                      =  plusPreservesPositivity x y zLTdx zLTdy in        
>   let z'             :  Fraction
>                      =  reduce alg z in
>   let n'             :  Nat
>                      =  num z' in
>   let d'             :  Nat
>                      =  den z' in
>   let zLTd'          :  (Z `LT` d')
>                      =  reducePreservesPositivity alg z zLTdz in
>   let n'd'coprime    :  (Coprime n' d')
>                      =  reduceYieldsCoprimes alg z zLTdz in
>   let gcdOne'        :  (gcd (alg n' d') = S Z)
>                      =  gcdOneCoprimeLemma2 n' d' alg n'd'coprime in 
> -}
>                      
>     ( fromFraction (x + y) (plusPreservesPositivity x y zLTdx zLTdy) )
>   ={ Refl }=
>     ( MkNonNegQ (num (reduce alg (x + y))) 
>                 (den (reduce alg (x + y))) 
>                 (reducePreservesPositivity alg (x + y) (plusPreservesPositivity x y zLTdx zLTdy)) 
>                 (gcdOneCoprimeLemma2 (num (reduce alg (x + y))) 
>                                      (den (reduce alg (x + y)))
>                                      alg 
>                                      (reduceYieldsCoprimes alg (x + y) (plusPreservesPositivity x y zLTdx zLTdy))) )
>   {-
>   ={ ?s2 }=
>     ( MkNonNegQ (num (reduce alg (reduce alg x + reduce alg y))) 
>                 (den (reduce alg (reduce alg x + reduce alg y))) 
>                 s21? s22? )
>   ={ ?s3 }=
>     ( fromFraction (reduce alg x + reduce alg y) 
>                    (plusPreservesPositivity (toFraction (MkNonNegQ nx' dx' zLTdx' nx'dx'gcd1)) 
>                                             (toFraction (MkNonNegQ ny' dy' zLTdy' ny'dy'gcd1)) 
>                                             (toFractionPreservesDenominatorPositivity (MkNonNegQ nx' dx' zLTdx' nx'dx'gcd1)) 
>                                             (toFractionPreservesDenominatorPositivity (MkNonNegQ ny' dy' zLTdy' ny'dy'gcd1))) )
>   -}
>   ={ ?s4 }=
>     ( fromFraction ((nx', dx') + (ny', dy'))
>                    (plusPreservesPositivity (toFraction (MkNonNegQ nx' dx' zLTdx' nx'dx'gcd1)) 
>                                             (toFraction (MkNonNegQ ny' dy' zLTdy' ny'dy'gcd1)) 
>                                             (toFractionPreservesDenominatorPositivity (MkNonNegQ nx' dx' zLTdx' nx'dx'gcd1)) 
>                                             (toFractionPreservesDenominatorPositivity (MkNonNegQ ny' dy' zLTdy' ny'dy'gcd1))) )
>   ={ Refl }=
>     ( fromFraction (fqx' + fqy') zLTdfqx'fqy' )
>   ={ Refl }=
>     ( fromFraction (toFraction qx' + toFraction qy') 
>                    (plusPreservesPositivity (toFraction qx') (toFraction qy') zLTdqx' zLTdqy') )
>   ={ Refl }=
>     ( MkNonNegQ nx' dx' zLTdx' nx'dx'gcd1 + MkNonNegQ ny' dy' zLTdy' ny'dy'gcd1 )
>   ={ Refl }=
>     ( fromFraction x zLTdx + fromFraction y zLTdy )
>   QED
> %freeze fromFractionLinear


> ||| Addition is commutative
> plusCommutative : (x : NonNegQ) -> (y : NonNegQ) -> x + y = y + x
> plusCommutative x y = 
>   let x' = toFraction x in
>   let y' = toFraction y in
>   let zLTdx' = toFractionPreservesDenominatorPositivity x in
>   let zLTdy' = toFractionPreservesDenominatorPositivity y in
>   let zLTdx'y' = plusPreservesPositivity x' y' zLTdx' zLTdy' in
>   let zLTdy'x' = plusPreservesPositivity y' x' zLTdy' zLTdx' in
>     ( x + y )
>   ={ Refl }=
>     ( fromFraction (x' + y') zLTdx'y' )
>   ={ fromFractionLemma2 (x' + y') zLTdx'y' (y' + x') zLTdy'x' (plusCommutative x' y') }=
>     ( fromFraction (y' + x') (plusPreservesPositivity y' x' zLTdy' zLTdx') )    
>   ={ Refl }=
>     ( y + x )
>   QED
> %freeze plusCommutative


> ||| Addition is associative
> plusAssociative : (x : NonNegQ) -> (y : NonNegQ) -> (z : NonNegQ) -> x + (y + z) = (x + y) + z
> plusAssociative x y z = 
>   let x' = toFraction x in
>   let y' = toFraction y in
>   let z' = toFraction z in
>   let zLTdx' = toFractionPreservesDenominatorPositivity x in
>   let zLTdy' = toFractionPreservesDenominatorPositivity y in
>   let zLTdz' = toFractionPreservesDenominatorPositivity z in
>   let zLTdyz' = toFractionPreservesDenominatorPositivity (y + z) in
>   let zLTdx'yz' = plusPreservesPositivity (toFraction x) (toFraction (y + z)) zLTdx' zLTdyz' in
>   
>   let zLTdy'z' = plusPreservesPositivity (toFraction y) (toFraction z) zLTdy' zLTdz' in
>   let zLTdx'py'z' = plusPreservesPositivity (toFraction x) (toFraction y + toFraction z) zLTdx' zLTdy'z' in
>   let zLTdx'y' = plusPreservesPositivity (toFraction x) (toFraction y) zLTdx' zLTdy' in
>   let zLTdx'y'pz' = plusPreservesPositivity (toFraction x + toFraction y) (toFraction z) zLTdx'y' zLTdz' in
>   
>     ( x + (y + z) )
>   ={ Refl }=
>     ( fromFraction (toFraction x + toFraction (y + z)) zLTdx'yz' )
>   ={ fromFractionLinear (toFraction x) zLTdx' (toFraction (y + z)) zLTdyz' }=
>     ( fromFraction (toFraction x) zLTdx' + fromFraction (toFraction (y + z)) zLTdyz' )  
>   ={ replace {x = fromFraction (toFraction (y + z)) zLTdyz'}
>              {y = y + z}
>              {P = \ ZUZU => fromFraction (toFraction x) zLTdx' + fromFraction (toFraction (y + z)) zLTdyz'
>                             =
>                             fromFraction (toFraction x) zLTdx' + ZUZU}
>              (fromFractionToFractionLemma (y + z)) Refl }=
>     ( fromFraction (toFraction x) zLTdx' + (y + z) )  
>   ={ Refl }=
>     ( fromFraction (toFraction x) zLTdx' + fromFraction (toFraction y + toFraction z) zLTdy'z' )
>   ={ sym (fromFractionLinear (toFraction x) zLTdx' (toFraction y + toFraction z) zLTdy'z') }=
>     ( fromFraction (toFraction x + (toFraction y + toFraction z)) zLTdx'py'z' )  
>   ={ fromFractionLemma2 (toFraction x + (toFraction y + toFraction z)) 
>                         zLTdx'py'z' 
>                         ((toFraction x + toFraction y) + toFraction z) 
>                         zLTdx'y'pz' 
>                         (plusAssociative (toFraction x) (toFraction y) (toFraction z)) }=
>     ( fromFraction ((toFraction x + toFraction y) + toFraction z) zLTdx'y'pz' )    
>   ={ ?proof_in_reverse }=
>     ( (x + y) + z )
>   QED
> %freeze plusAssociative


> ||| Multiplication is commutative
> multCommutative : (x : NonNegQ) -> (y : NonNegQ) -> x * y = y * x
> multCommutative x y = 
>   let x' = toFraction x in
>   let y' = toFraction y in
>   let zLTdx' = toFractionPreservesDenominatorPositivity x in
>   let zLTdy' = toFractionPreservesDenominatorPositivity y in
>   let zLTdx'y' = multPreservesPositivity x' y' zLTdx' zLTdy' in
>   let zLTdy'x' = multPreservesPositivity y' x' zLTdy' zLTdx' in
>     ( x * y )
>   ={ Refl }=
>     ( fromFraction (x' * y') zLTdx'y' )
>   ={ fromFractionLemma2 (x' * y') zLTdx'y' (y' * x') zLTdy'x' (multCommutative x' y') }=
>     ( fromFraction (y' * x') (multPreservesPositivity y' x' zLTdy' zLTdx') )    
>   ={ Refl }=
>     ( y * x )
>   QED
> %freeze multCommutative


> {-

> fromFractionNumLemma : (n : Nat) -> (d : Nat) -> (zLTd : Z `LT` d) -> 
>                        num (fromFraction n d zLTd) * (gcd (alg n d)) = n

> fromFractionDenLemma : (n : Nat) -> (d : Nat) -> (zLTd : Z `LT` d) -> 
>                        den (fromFraction n d zLTd) * (gcd (alg n d)) = d

In order to implement simple probability distributions based on
non-negative rational numbers, we need these to fulfill

> plusZeroPlusRight : (x : NonNegQ) -> x + (fromInteger 0) = x
> plusZeroPlusRight (MkNonNegQ n d zLTd gcdOne) = s7 where
>   s1 : (MkNonNegQ n d zLTd gcdOne) + (fromInteger 0)
>        =
>        (MkNonNegQ n d zLTd gcdOne) + MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z)
>   s1 = Refl
>   s2 : (MkNonNegQ n d zLTd gcdOne) + MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z)
>        =
>        fromFraction (n * (S Z) + Z * d)
>                     (d * (S Z))
>                     (multZeroLTZeroLT d (S Z) zLTd (ltZS Z))
>   s2 = Refl
>   s3 : n * (S Z) + Z * d = n
>   s3 = ( n * (S Z) + Z * d )
>      ={ replace {x = n * (S Z)}
>                 {y = n}
>                 {P = \ ZUZU => n * (S Z) + Z * d = ZUZU + Z * d}
>                 (multOneRightNeutral n) Refl}=
>        ( n + Z * d )
>      ={ replace {x = Z * d}
>                 {y = Z}
>                 {P = \ ZUZU => n + Z * d = n + ZUZU}
>                 (multZeroLeftZero d) Refl }=
>        ( n + Z )
>      ={ plusZeroRightNeutral n }=
>        ( n )
>      QED
>   s4 : d * (S Z) = d
>   s4 = multOneRightNeutral d
>   s5 : fromFraction (n * (S Z) + Z * d)
>                     (d * (S Z))
>                     (multZeroLTZeroLT d (S Z) zLTd (ltZS Z))
>        =
>        fromFraction n d zLTd
>   s5 = fromFractionLemma2 (n * (S Z) + Z * d) (d * (S Z))
>                           (multZeroLTZeroLT d (S Z) zLTd (ltZS Z))
>                           n d zLTd s3 s4
>   s6 : fromFraction n d zLTd = MkNonNegQ n d zLTd gcdOne
>   s6 = fromFractionLemma1 n d zLTd gcdOne
>   s7 : (MkNonNegQ n d zLTd gcdOne) + (fromInteger 0) = (MkNonNegQ n d zLTd gcdOne)
>   s7 = trans s1 (trans s2 (trans s5 s6))


> {-
> plusZeroPlusLeft  : (x : NonNegQ) -> (fromInteger 0) + x = x
> plusZeroPlusLeft x@(MkNonNegQ n d zLTd gcdOne) =
>     (  (fromInteger 0) + x  )
>   ={ Refl }=
>     (  MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z)   +   MkNonNegQ n d zLTd gcdOne  )
>   ={ Refl }=
>     ( let n' = Z * d + n * (S Z)
>           d' = (S Z) * d
>           -- zLTd' : Z `LT` d'
>           zLTd' = multZeroLTZeroLT (S Z) d (zeroLTden (fromInteger 0)) zLTd
>       in  fromFraction n' d' zLTd' )
>   ={ ?pZPL }=
>     ( MkNonNegQ n d zLTd gcdOne )
>   ={ Refl }=
>      x
>   QED
> -}

> {- TODO: complete
> multZeroPlusRight : (x : NonNegQ) -> x * (fromInteger 0) = fromInteger 0
> multZeroPlusRight x@(MkNonNegQ n d zLTd gcdOne) =
>     (  x * (fromInteger 0)  )
>   ={ Refl }=
>     (  (MkNonNegQ n d zLTd gcdOne) * (MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z))  )
>   ={ Refl }=
>     (  fromFraction (n * Z) (d * (S Z)) (multZeroLTZeroLT d (S Z) zLTd (zeroLTden (fromInteger 0))))
>   ={ ?foo }=
>     (  fromInteger 0  )
>   QED
> -}

> {-

> multZeroPlusLeft  : (x : NonNegQ) -> (fromInteger 0) * x = fromInteger 0

> multOneRight      : (x : NonNegQ) -> x * (fromInteger 1) = x

> multOneLeft       : (x : NonNegQ) -> (fromInteger 1) * x = x


> multDistributesOverPlusRight : (x : NonNegQ) -> (y : NonNegQ) -> (z : NonNegQ) ->
>                                x * (y + z) = (x * y) + (x * z)

> multDistributesOverPlusLeft  : (x : NonNegQ) -> (y : NonNegQ) -> (z : NonNegQ) ->
>                                (x + y) * z = (x * z) + (y * z)

> -}

> ---}
 
