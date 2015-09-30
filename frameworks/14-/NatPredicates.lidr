> module NatPredicates

> %default total


Divisor (following an idea from Tim Richter):

> {-
> data Divisor : (m : Nat) -> (n : Nat) -> Type where
>   mkDivisor : (m : Nat) -> (n : Nat) -> Exists (\ q => m * q = n) -> Divisor m n
> -}

> Divisor : (m : Nat) -> (n : Nat) -> Type
> Divisor m n = Exists (\ q => m * q = n)

Greatest common divisor (following an idea from Tim Richter):

> data GCD : (d : Nat) -> (m : Nat) -> (n : Nat) -> Type where
>   mkGCD : d `Divisor` m ->
>           d `Divisor` n ->
>           ((d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d) ->
>           GCD d m n

> gcd : (d : Nat ** GCD d m n) -> Nat
> gcd = getWitness

> gcdDivisorFst : GCD d m n -> d `Divisor` m
> gcdDivisorFst {d} (mkGCD dDm dDn dG) = dDm

> gcdDivisorSnd : GCD d m n -> d `Divisor` n
> gcdDivisorSnd {d} (mkGCD dDm dDn dG) = dDn

> gcdDivisorGreatest : GCD d m n -> ((d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d)
> gcdDivisorGreatest {d} (mkGCD dDm dDn dG) = dG


Coprime (following an idea from Tim Richter):

> data Coprime : (m : Nat) -> (n : Nat) -> Type where
>   mkCoprime : GCD d m n -> d = S Z -> Coprime m n
