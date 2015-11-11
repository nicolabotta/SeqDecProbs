> module NonNegRational


> import NatGCD
> import NatGCDOperations
> import NatGCDEuclid


> %default total


< ||| Non negative rationals
< data NonNegQ : Type where
<   MkNonNegQ : (n : Nat) -> (d : Nat) -> Not (d = Z) -> Coprime n d -> NonNegQ

This approach seems quite natural but there is a problem: both |Not (d =
Z)| and |Coprime n d| are not unique. Because of this, one can easily
contruct rational numbers which are syntactically different and yet
share the same values for numerator and denominator. This is not very
good.

Non uniqueness of |Not (d = Z)| and |Coprime n d| also becomes a problem
when one tries to prove properties of operations on rational
numbers, for instance

< plusZeroPlusRight : (x : NonNegQ) -> x + (fromInteger 0) = x

see NonNegRationalProperties.lidr. The problem here is that |x +
(fromInteger 0)| is defined in terms of some implementation of |(+)|
which, in one way or another, will call |MkNonNegQ| with argument proofs
that do not generally reduce to with those used to built |x|. Without
uniqueness of |Not (d = Z)| and |Coprime n d| (or ad-hoc implementations
of |(+)|) it is hardly possible to prove |plusZeroPlusRight|.

We can easily replace |Not (d = Z)| with |Z `LT` d| and take advantage
of uniqueness of |LT|:

< ||| Non negative rationals
< data NonNegQ : Type where
<   MkNonNegQ : (n : Nat) -> (d : Nat) -> Z `LT` d -> Coprime n d -> NonNegQ

In order to replace |Coprime n d| with some equivalent unique property
it is useful to notice that (see NatProperties.lidr):

< gcdOneCoprimeLemma1 : (alg : (a : Nat) -> (b : Nat) -> (d : Nat ** GCD d a b)) ->
<                       (m : Nat) -> (n : Nat) ->
<                       gcd (alg m n) = S Z -> Coprime m n

< gcdOneCoprimeLemma2 : (m : Nat) -> (n : Nat) ->
<                       (alg : (a : Nat) -> (b : Nat) -> (d : Nat ** GCD d a b)) ->
<                       Coprime m n -> gcd (alg m n) = S Z

This suggests the following definition of non-negative rational numbers:

> ||| The GCD algorithm
> alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)
> alg = euclidGCD

> ||| Non negative rationals
> data NonNegQ : Type where
>   MkNonNegQ : (n : Nat) -> (d : Nat) -> Z `LT` d -> gcd (alg n d) = S Z -> NonNegQ


