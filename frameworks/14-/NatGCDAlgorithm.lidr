> module NatGCDAlgorithm


> import NatGCD
> import NatGCDProperties
> import NatGCDEuclid
> import PairsOperations
> import Sigma


> %default total

> %access public export

> %hide gcd


> ||| The GCD algorithm
> gcdAlg : Nat -> Nat -> Nat
> gcdAlg m n = getWitness (euclidGCD m n)

> gcdAlgLemma : (m : Nat) -> (n : Nat) -> GCD (gcdAlg m n) m n
> gcdAlgLemma m n = getProof (euclidGCD m n)

> gcdAlgCommutative : (m : Nat) -> (n : Nat) -> gcdAlg m n = gcdAlg n m
> gcdAlgCommutative m n =
>   let d1  :  Nat
>           =  gcdAlg m n in
>   let d2  :  Nat
>           =  gcdAlg n m in
>   let v1  :  GCD d1 m n 
>           =  gcdAlgLemma m n in
>   let v2  :  GCD d2 m n 
>           =  gcdCommutative (gcdAlgLemma n m) in
>   gcdUnique d1 d2 v1 v2

