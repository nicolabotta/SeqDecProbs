> module FractionNormal

> import Fraction


> %default total
> %access public export


> data Normal : Fraction -> Type where
>   MkNormal  : {x : Fraction} -> Normal x


