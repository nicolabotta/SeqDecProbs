> module NatGCDEuclidStrippedDown


> import NatOperations
> import NatProperties


> %default total


Euclid's greatest common divisor algorithm

> {-
> %assert_total
> euclidGCD : (m : Nat) -> (n : Nat) -> Nat
> euclidGCD    m   Z    = m
> euclidGCD  Z       n  = n
> euclidGCD (S m) (S n) with (decLTE (S m) (S n))
>   | (Yes p) = euclidGCD (S m) (S n - S m)
>   | (No  p) = euclidGCD (S m - S n) (S n)
> ---}


> --{-
> %assert_total
> euclidGCD : (m : Nat) -> (n : Nat) -> Nat
> euclidGCD    m   Z    = m
> euclidGCD  Z       n  = n
> euclidGCD (S m) (S n) = if (m <= n) 
>                         then euclidGCD (S m) (S n - S m)
>                         else euclidGCD (S m - S n) (S n)
> ---}
