> module NatPredicates

> import Sigma

> %default total
> %access public export
> %auto_implicits on


Divisor (following an idea from Tim Richter):

> {-
> data Divisor : (m : Nat) -> (n : Nat) -> Type where
>   mkDivisor : (m : Nat) -> (n : Nat) -> Exists (\ q => m * q = n) -> Divisor m n
> -}

> Divisor : (m : Nat) -> (n : Nat) -> Type
> Divisor m n = Exists (\ q => m * q = n)


Greatest common divisor (following an idea from Tim Richter):

> data GCD : (d : Nat) -> (m : Nat) -> (n : Nat) -> Type where
>   MkGCD : d `Divisor` m ->
>           d `Divisor` n ->
>           ((d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d) ->
>           GCD d m n

> gcd : Sigma Nat (\ d => GCD d m n) -> Nat
> gcd (MkSigma d _) = d

> gcdDivisorFst : GCD d m n -> d `Divisor` m
> gcdDivisorFst {d} (MkGCD dDm dDn dG) = dDm

> gcdDivisorSnd : GCD d m n -> d `Divisor` n
> gcdDivisorSnd {d} (MkGCD dDm dDn dG) = dDn

> gcdDivisorGreatest : GCD d m n -> ((d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d)
> gcdDivisorGreatest {d} (MkGCD dDm dDn dG) = dG


Coprime (following an idea from Tim Richter):

> data Coprime : (m : Nat) -> (n : Nat) -> Type where
>   MkCoprime : GCD d m n -> d = S Z -> Coprime m n
