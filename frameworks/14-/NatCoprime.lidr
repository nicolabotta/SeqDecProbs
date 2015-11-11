> module NatCoprime


> import NatGCD


> %default total


> ||| 
> data Coprime : (m : Nat) -> (n : Nat) -> Type where
>   MkCoprime : GCD d m n -> d = S Z -> Coprime m n
