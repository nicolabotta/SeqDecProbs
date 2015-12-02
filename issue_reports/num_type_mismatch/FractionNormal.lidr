> module FractionNormal

> import Fraction


> %default total


> data Normal : Fraction -> Type where
>   MkNormal  : {x : Fraction} -> Normal x


