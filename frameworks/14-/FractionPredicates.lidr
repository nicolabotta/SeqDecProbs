> module FractionPredicates


> import Fraction
> -- import FractionOperations
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





