> module NatPredicates


> %default total


> ||| m and n are coprime iff their gcd is one
> Coprime : Nat -> Nat -> Type
> Coprime m n = gcd m n = S Z

