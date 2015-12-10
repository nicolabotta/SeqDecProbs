> module NatGCDEuclidStrippedDown


> import NatOperations
> import NatProperties


> %default total


Euclid's greatest common divisor algorithm


> --{-
> %assert_total
> euclidGCD : (m : Nat) -> (n : Nat) -> Nat
> euclidGCD    m   Z    = m
> euclidGCD  Z       n  = n
> euclidGCD (S m) (S n) with (decLTE (S m) (S n))
>   | (Yes p) = euclidGCD (S m) (S n - S m)
>   | (No  p) = euclidGCD (S m - S n) (S n)
> ---}


> {-
> %assert_total
> euclidGCD : (m : Nat) -> (n : Nat) -> Nat
> euclidGCD    m   Z    = m
> euclidGCD  Z       n  = n
> euclidGCD (S m) (S n) with (decEq m n)
>   | (Yes _) = S m
>   | (No  _) with (decEq (m - n) Z)
>     | (Yes _) = euclidGCD (S m) (S n - S m)
>     | (No  _) = euclidGCD (S m - S n) (S n)
> ---}


> {-
> %assert_total
> euclidGCD : (m : Nat) -> (n : Nat) -> Nat
> euclidGCD    m   Z    = m
> euclidGCD  Z       n  = n
> euclidGCD (S m) (S n) = if (S m <= S n) 
>                         then euclidGCD (S m) (S n - S m)
>                         else euclidGCD (S m - S n) (S n)
> ---}
