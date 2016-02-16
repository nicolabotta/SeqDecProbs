> module NatCoprime


> import NatGCD
> import NatGCDAlgorithm
> import Unique
> import EqualityProperties
> import NatGCDEuclid
> import PairsOperations
> import Sigma


> %default total

> %access public export


> ||| 
> data Coprime : (m : Nat) -> (n : Nat) -> Type where
>   MkCoprime : {m, n : Nat} -> gcdAlg m n = S Z -> Coprime m n


> |||
> CoprimeUnique : {m, n : Nat} -> Unique (Coprime m n)
> CoprimeUnique {m} {n} (MkCoprime p) (MkCoprime q) = cong (uniqueEq (gcdAlg m n) (S Z) p q)
