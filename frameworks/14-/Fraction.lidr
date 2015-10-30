> module Fraction

> import Syntax.PreorderReasoning

> import NatPredicates
> import NatOperations
> import NatProperties


> %default total


> Fraction : Type
> Fraction = (Nat, Nat)


Operations

> ||| The numerator of a fraction
> num : Fraction -> Nat
> num = fst
> -- %freeze num

> ||| The denominator of a fraction
> den : Fraction -> Nat
> den = snd
> -- %freeze den

> ||| Every natural number is a fraction
> fromNat : Nat -> Fraction
> fromNat n = (n, S Z)
> -- %freeze fromNat

> ||| Reduction to normal form (coprime numbers)
> reduce : ((m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>          Fraction -> Fraction
> reduce alg (n, d) with (decCoprime alg n d)
>   | (Yes _) = (n, d)
>   | (No  _) = (n', d') where
>       gcdv : (gcd : Nat ** GCD gcd n d)
>       gcdv = alg n d
>       gcd : Nat
>       gcd = getWitness gcdv
>       v : GCD gcd n d
>       v = getProof gcdv
>       n' : Nat
>       n' = divBy gcd n (gcdDivisorFst v)
>       d' : Nat
>       d' = divBy gcd d (gcdDivisorSnd v)
> -- %freeze reduce

> ||| Fraction addition
> plus : Fraction -> Fraction -> Fraction
> plus (n1, d1) (n2, d2) = (n1 * d2 + n2 * d1, d1 * d2)
> -- %freeze plus

> ||| Fraction multiplication
> mult : Fraction -> Fraction -> Fraction
> mult (n1, d1) (n2, d2) = (n1 * n2, d1 * d2)
> -- %freeze mult


Properties of |num|, |den|:

> ||| The denominator preserves equality
> denPreservesEquality : (x : Fraction) -> (y : Fraction) -> x = y -> den x = den y
> denPreservesEquality (n, d) (n, d) Refl = Refl


Properties of |reduce|:

> ||| First reduce lemma
> reduceLemmaNum : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>                  (x : Fraction) -> 
>                  Sigma Nat (\ gcd => num x = (num (reduce alg x)) * gcd)
> reduceLemmaNum alg (n, d) with (decCoprime alg n d)
>   | (Yes _) = (1 ** sym (multOneRightNeutral n))
>   | (No  _) = (gcd ** ?lika)  where
>       gcdv : (gcd : Nat ** GCD gcd n d)
>       gcdv = alg n d
>       gcd : Nat
>       gcd = getWitness gcdv
>       v : GCD gcd n d
>       v = getProof gcdv
>       n' : Nat
>       n' = divBy gcd n (gcdDivisorFst v)
>       d' : Nat
>       d' = divBy gcd d (gcdDivisorSnd v)

> ||| Second reduce lemma
> reduceLemmaDen : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>                  (x : Fraction) -> 
>                  Sigma Nat (\ gcd => den x = (den (reduce alg x)) * gcd)

> ||| Reduction of coprime numbers is identity
> reducePreservesCoprimes : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>                           (x : Fraction) -> 
>                           Coprime (num x) (den x) -> 
>                           reduce alg x = x                       
> reducePreservesCoprimes alg (n, d) prf with (decCoprime alg n d)
>   | (Yes _) = Refl
>   | (No  contra) = void (contra prf)
> %freeze reducePreservesCoprimes


> ||| Reduction preserves denominator positivity
> reducePreservesPositivity : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>                             (x : Fraction) -> Z `LT` den x -> 
>                             Z `LT` den (reduce alg x)
> reducePreservesPositivity alg (n, d) zLTd with (decCoprime alg n d)
>   | (Yes _) = zLTd
>   | (No _) = divByPreservesPositivity gcd d gcdDd zLTd where
>     gcd : Nat
>     gcd = getWitness (alg n d)
>     gcdDd : gcd `Divisor` d
>     gcdDd = gcdDivisorSnd (getProof (alg n d))
> %freeze reducePreservesPositivity


> ||| Reduction yields coprime numbers
> reduceYieldsCoprimes : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>                        (x : Fraction) -> Z `LT` den x -> 
>                        Coprime (num (reduce alg x)) (den (reduce alg x))
> reduceYieldsCoprimes alg (n, d) zLTdx with (decCoprime alg n d)
>   | (Yes prf) = prf
>   | (No _) = gcdCoprimeLemma'' (getProof (alg n d)) (gcdPreservesPositivity2 zLTdx (alg n d))
> %freeze reduceYieldsCoprimes


> ||| Reduction is idempotent (not used)
> -- reduceIdempotent : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
> --                    (x : Fraction) ->
> --                    reduce alg (reduce alg x) = reduce alg x
> -- -- %freeze reduceIdempotent


> ||| Fraction is an instance of Num
> instance Num Fraction where
>   (+) = plus
>   (*) = mult
>   fromInteger = Fraction.fromNat . fromIntegerNat


> ||| Reduction is "linear"
> reduceLinear : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>                (x : Fraction) -> (y : Fraction) ->
>                reduce alg (x + y) = reduce alg (reduce alg x + reduce alg y)
> reduceLinear alg (n1, d1) (n2, d2) =
>   let gcdv1  :  (lala : Nat ** GCD lala n1 d1)
>              =  alg n1 d1 in
>   let gcd1   :  Nat
>              =  getWitness gcdv1 in
>   let gcdv2  :  (lala : Nat ** GCD lala n2 d2)
>              =  alg n2 d2 in
>   let gcd2   :  Nat
>              =  getWitness gcdv2 in
>     ( reduce alg ((n1, d1) + (n2, d2)) )
>   ={ Refl }=
>     ( reduce alg (n1 * d2 + n2 * d1, d1 * d2) )
>   ={ ?s1 }=
>     ( reduce alg (reduce alg (n1, d1) + reduce alg (n2, d2)) )
>   QED  
> %freeze reduceLinear


> ||| Addition preserves denominator positivity
> plusPreservesPositivity : (x : Fraction) -> (y : Fraction) -> 
>                           Z `LT` den x -> Z `LT` den y -> Z `LT` den (x + y)
> plusPreservesPositivity (n1, d1) (n2, d2) p q = multZeroLTZeroLT (den (n1, d1)) (den (n2, d2)) p q
> %freeze plusPreservesPositivity


> ||| Multiplication preserves denominator positivity
> multPreservesPositivity : (x : Fraction) -> (y : Fraction) -> 
>                           Z `LT` den x -> Z `LT` den y -> Z `LT` den (x * y)
> multPreservesPositivity (n1, d1) (n2, d2) p q = multZeroLTZeroLT (den (n1, d1)) (den (n2, d2)) p q
> %freeze multPreservesPositivity


> ||| Addition is commutative
> plusCommutative : (x : Fraction) -> (y : Fraction) -> x + y = y + x
> plusCommutative (n1, d1) (n2, d2) = 
>     ( (n1, d1) + (n2, d2) )
>   ={ Refl }=
>     ( (n1 * d2 + n2 * d1, d1 * d2) )
>   ={ replace {x = n1 * d2 + n2 * d1}
>              {y = n2 * d1 + n1 * d2}
>              {P = \ ZUZU => (n1 * d2 + n2 * d1, d1 * d2) = (ZUZU, d1 * d2)}
>              (Nat.plusCommutative (n1 * d2) (n2 * d1)) Refl }=
>     ( (n2 * d1 + n1 * d2, d1 * d2) )
>   ={ replace {x = d1 * d2}
>              {y = d2 * d1}
>              {P = \ ZUZU => (n2 * d1 + n1 * d2, d1 * d2) = (n2 * d1 + n1 * d2, ZUZU)}
>              (Nat.multCommutative d1 d2) Refl }=           
>     ( (n2 * d1 + n1 * d2, d2 * d1) )
>   ={ Refl }=
>     ( (n2, d2) + (n1, d1) )
>   QED
> %freeze plusCommutative


> ||| |fromInteger 0| is neutral element of addition
> plusZeroPlusRight : (x : Fraction) -> x + (fromInteger 0) = x
> plusZeroPlusRight (n, d) =
>     ( (n, d) + (fromInteger 0) )
>   ={ Refl }=
>     ( (n, d) + (Z, S Z) )
>   ={ Refl }=
>     ( (n * (S Z) + Z * d, d * (S Z)) )
>   ={ replace {x = n * (S Z)}
>              {y = n}
>              {P = \ ZUZU => (n * (S Z) + Z * d, d * (S Z)) = (ZUZU + Z * d, d * (S Z))}
>              (multOneRightNeutral n) Refl }=
>     ( (n + Z * d, d * (S Z)) )
>   ={ Refl }=
>     ( (n + Z, d * (S Z)) )
>   ={ replace {x = n + Z}
>              {y = n}
>              {P = \ ZUZU => (n + Z, d * (S Z)) = (ZUZU, d * (S Z))}
>              (plusZeroRightNeutral n) Refl }=
>     ( (n, d * (S Z)) )
>   ={ replace {x = d * (S Z)}
>              {y = d}
>              {P = \ ZUZU => (n, d * (S Z)) = (n, ZUZU)}
>              (multOneRightNeutral d) Refl }=
>     ( (n, d) )
>   QED
> %freeze plusZeroPlusRight


> ||| |fromInteger 0| is neutral element of addition
> plusZeroPlusLeft  : (x : Fraction) -> (fromInteger 0) + x = x
> plusZeroPlusLeft x = 
>     ( (fromInteger 0) + x )
>   ={ plusCommutative (fromInteger 0) x }=
>     ( x + (fromInteger 0) )
>   ={ plusZeroPlusRight x }=
>     ( x )
>   QED
> %freeze plusZeroPlusLeft


> ||| Addition is associative
> plusAssociative : (x : Fraction) -> (y : Fraction) -> (z : Fraction) -> x + (y + z) = (x + y) + z
> plusAssociative (n1, d1) (n2, d2) (n3, d3) =
>     ( (n1, d1) + ((n2, d2) + (n3, d3)) )
>   ={ Refl }=
>     ( (n1, d1) + (n2 * d3 + n3 * d2, d2 * d3) )
>   ={ Refl }=
>     ( (n1 * (d2 * d3) + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3)) )
>   ={ replace {x = n1 * (d2 * d3)}
>              {y = (n1 * d2) * d3}
>              {P = \ ZUZU => (n1 * (d2 * d3) + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3))
>                             =
>                             (ZUZU + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3))}
>              (multAssociative n1 d2 d3) Refl }=
>     ( ((n1 * d2) * d3 + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3)) )
>   ={ replace {x = (n2 * d3 + n3 * d2) * d1}
>              {y = (n2 * d3) * d1 + (n3 * d2) * d1}
>              {P = \ ZUZU => ((n1 * d2) * d3 + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3))
>                             =
>                             ((n1 * d2) * d3 + (ZUZU), d1 * (d2 * d3))}
>              (multDistributesOverPlusLeft (n2 * d3) (n3 * d2) d1) Refl }=
>     ( ((n1 * d2) * d3 + ((n2 * d3) * d1 + (n3 * d2) * d1), d1 * (d2 * d3)) )
>   ={ replace {x = (n2 * d3) * d1}
>              {y = n2 * (d3 * d1)}
>              {P = \ ZUZU => ((n1 * d2) * d3 + ((n2 * d3) * d1 + (n3 * d2) * d1), d1 * (d2 * d3))
>                             =
>                             ((n1 * d2) * d3 + (ZUZU + (n3 * d2) * d1), d1 * (d2 * d3))}
>              (sym (multAssociative n2 d3 d1)) Refl }=
>     ( ((n1 * d2) * d3 + (n2 * (d3 * d1) + (n3 * d2) * d1), d1 * (d2 * d3)) )
>   ={ replace {x = d3 * d1}
>              {y = d1 * d3}
>              {P = \ ZUZU => ((n1 * d2) * d3 + (n2 * (d3 * d1) + (n3 * d2) * d1), d1 * (d2 * d3))
>                             =
>                             ((n1 * d2) * d3 + (n2 * (ZUZU) + (n3 * d2) * d1), d1 * (d2 * d3))}
>              (multCommutative d3 d1) Refl }=
>     ( ((n1 * d2) * d3 + (n2 * (d1 * d3) + (n3 * d2) * d1), d1 * (d2 * d3)) )
>   ={ replace {x = n2 * (d1 * d3)}
>              {y = (n2 * d1) * d3}
>              {P = \ ZUZU => ((n1 * d2) * d3 + (n2 * (d1 * d3) + (n3 * d2) * d1), d1 * (d2 * d3))
>                             =
>                             ((n1 * d2) * d3 + (ZUZU + (n3 * d2) * d1), d1 * (d2 * d3))}
>              (multAssociative n2 d1 d3) Refl }=
>     ( ((n1 * d2) * d3 + ((n2 * d1) * d3 + (n3 * d2) * d1), d1 * (d2 * d3)) )
>   ={ replace {x = (n1 * d2) * d3 + ((n2 * d1) * d3 + (n3 * d2) * d1)}
>              {y = ((n1 * d2) * d3 + (n2 * d1) * d3) + (n3 * d2) * d1}
>              {P = \ ZUZU => ((n1 * d2) * d3 + ((n2 * d1) * d3 + (n3 * d2) * d1), d1 * (d2 * d3))
>                             =
>                             (ZUZU, d1 * (d2 * d3))}
>              (plusAssociative ((n1 * d2) * d3) ((n2 * d1) * d3) ((n3 * d2) * d1)) Refl }=
>     ( (((n1 * d2) * d3 + (n2 * d1) * d3) + (n3 * d2) * d1, d1 * (d2 * d3)) )
>   ={ replace {x = (n3 * d2) * d1}
>              {y = n3 * (d2 * d1)}
>              {P = \ ZUZU => (((n1 * d2) * d3 + (n2 * d1) * d3) + (n3 * d2) * d1, d1 * (d2 * d3))
>                             =
>                             (((n1 * d2) * d3 + (n2 * d1) * d3) + ZUZU, d1 * (d2 * d3))}
>              (sym (multAssociative n3 d2 d1)) Refl }=         
>     ( (((n1 * d2) * d3 + (n2 * d1) * d3) + n3 * (d2 * d1), d1 * (d2 * d3)) )
>   ={ replace {x = (n1 * d2) * d3 + (n2 * d1) * d3}
>              {y = (n1 * d2 + n2 * d1) * d3}
>              {P = \ ZUZU => (((n1 * d2) * d3 + (n2 * d1) * d3) + n3 * (d2 * d1), d1 * (d2 * d3))
>                             =
>                             (ZUZU + n3 * (d2 * d1), d1 * (d2 * d3))}
>              (sym (multDistributesOverPlusLeft (n1 * d2) (n2 * d1) d3)) Refl }=
>     ( ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), d1 * (d2 * d3)) )
>   ={ replace {x = d1 * (d2 * d3)}
>              {y = (d1 * d2) * d3}
>              {P = \ ZUZU => ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), d1 * (d2 * d3))
>                             =
>                             ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), ZUZU)}
>              (multAssociative d1 d2 d3) Refl }=  
>     ( ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), (d1 * d2) * d3) )
>   ={ replace {x = d2 * d1}
>              {y = d1 * d2}
>              {P = \ ZUZU => ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), (d1 * d2) * d3)
>                             =
>                             ((n1 * d2 + n2 * d1) * d3 + n3 * (ZUZU), (d1 * d2) * d3)}
>              (multCommutative d2 d1) Refl }=
>     ( ((n1 * d2 + n2 * d1) * d3 + n3 * (d1 * d2), (d1 * d2) * d3) )
>   ={ Refl }=
>     ( (n1 * d2 + n2 * d1, d1 * d2) + (n3, d3) )
>   ={ Refl }=
>     ( ((n1, d1) + (n2, d2)) + (n3, d3) )
>   QED
> %freeze plusAssociative


> ||| Multiplication is commutative
> multCommutative : (x : Fraction) -> (y : Fraction) -> x * y = y * x
> multCommutative (n1, d1) (n2, d2) = 
>     ( (n1, d1) * (n2, d2) )
>   ={ Refl }=
>     ( (n1 * n2, d1 * d2) )
>   ={ replace {x = n1 * n2}
>              {y = n2 * n1}
>              {P = \ ZUZU => (n1 * n2, d1 * d2) = (ZUZU, d1 * d2)}
>              (Nat.multCommutative n1 n2) Refl }=
>     ( (n2 * n1, d1 * d2) )
>   ={ replace {x = d1 * d2}
>              {y = d2 * d1}
>              {P = \ ZUZU => (n2 * n1, d1 * d2) = (n2 * n1, ZUZU)}
>              (Nat.multCommutative d1 d2) Refl }=           
>     ( (n2 * n1, d2 * d1) )
>   ={ Refl }=
>     ( (n2, d2) * (n1, d1) )
>   QED
> %freeze multCommutative


> |||
> multOneRight : (x : Fraction) -> x * (fromInteger 1) = x
> multOneRight (n, d) = 
>     ( (n, d) * (S Z, S Z) )
>   ={ Refl }=
>     ( (n * (S Z), d * (S Z)) )
>   ={ replace {x = n * (S Z)}
>              {y = n}
>              {P = \ ZUZU => (n * (S Z), d * (S Z)) = (ZUZU, d * (S Z))}
>              (multOneRightNeutral n) Refl }=
>     ( (n, d * (S Z)) )
>   ={ replace {x = d * (S Z)}
>              {y = d}
>              {P = \ ZUZU => (n, d * (S Z)) = (n, ZUZU)}
>              (multOneRightNeutral d) Refl }=           
>     ( (n, d) )
>   QED
> %freeze multOneRight


> |||
> multOneLeft : (x : Fraction) -> (fromInteger 1) * x = x
> multOneLeft x = 
>     ( (fromInteger 1) * x )
>   ={ multCommutative (fromInteger 1) x }=
>     ( x * (fromInteger 1) )
>   ={ multOneRight x }=
>     ( x )
>   QED
> %freeze multOneLeft



