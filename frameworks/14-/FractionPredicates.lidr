> module FractionPredicates

> import Fraction
> import PNat
> import PNatOperations

> %default total
> %access public export
> %auto_implicits off


> ||| Proofs that `x` is less than or equal to `y`                                                                          
> ||| @ x the smaller number                                                                                                
> ||| @ y the larger number
> LTE : (x, y : Fraction) -> Type
> LTE (n1, d1') (n2, d2') = Prelude.Nat.LTE (n1 * (toNat d2')) (n2 * (toNat d1'))


> ||| An equivalence relation (see below)
> Eq : Fraction -> Fraction -> Type
> Eq (m, d') (n, e') = let d = toNat d' in
>                      let e = toNat e' in
>                      m * e = n * d
> -- %freeze Eq

The idea is to use |Eq| implement non-negative rational numbers as
quotient of fractions by |Eq|. 

A naive approach toward implementing (non-negative) rational numbers
(for which equality is well represented by syntactical equality) could
be to define rational numbers as normalized fractions, something like

  NonNegRational = Subset Fraction Normal

where |Normal : Fraction -> Type| represents the property of being in
normal form, see "FractionNormal". It is easy to see that |normalize|
does indeed return fractions in normal form, see |normalNormalize| in
"FractionProperties". Thus, one could implement addition and
multiplication of rational numbers in terms of |normalize| and of
fraction addition and multiplication. For instance:

  plus : NonNegRational -> NonNegRational -> NonNegRational
  plus x' y' = let x   =  getWitness x' in
               let y   =  getWitness y' in
               Element (normalize (x + y)) (normalNormalize (x + y))

and similarly for multiplication. The problem with this approach is that
implementing proofs of

  1.  x + y = y + x
  2.  x + 0 = x
  3.  x + (y + z) = (x + y) + z
  4.  x * y = y * x
  5.  x * 1 = x

for fractions is tedious but trivial. Extending 1,2,4,5 to rational
numbers is pretty straightforward but extending 3 and deriving

  6.  x * (y + z) = (x * y) + (x * z)
  
(which does not hold for fractions) turns out to be a nightmare. With
|Eq| we can take advantage of Tim Richter's "SplitQuotient" and
"KernelQuotient" modules (see ...) to define ...

...

To this end, we only need to show that:

 a. Fraction addition and multiplication preserve Eq:

    a1.  (x Eq x') -> (y Eq y') -> (x + y) Eq (x' + y')   
    a2.  (x Eq x') -> (y Eq y') -> (x * y) Eq (x' * y')   

 b. Normalize fulfills: 

    b1.  (normalize x) Eq x
    b2.  x Eq y -> normalize x = normalize y

These properties are implemented via

< plusPreservesEq : (x, x', y, y' : Fraction) -> 
<                   (x `Eq` x') -> (y `Eq` y') -> (x + y) `Eq` (x' + y')

< multPreservesEq : (x, x', y, y' : Fraction) -> 
<                   (x `Eq` x') -> (y `Eq` y') -> (x * y) `Eq` (x' * y')
 
and
                  
< normalizeEqLemma1 : (x : Fraction) -> (normalize x) `Eq` x

< normalizeEqLemma2 : (x : Fraction) -> (y : Fraction) -> 
<                     x `Eq` y -> normalize x = normalize y

in "FractionEqProperties".





