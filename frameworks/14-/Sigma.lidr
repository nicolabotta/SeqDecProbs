> module Sigma

> %default total

> %access public export

> %hide Sigma
> %hide MkSigma


> data Sigma : (a : Type) -> (P : a -> Type) -> Type where                                                                
>   MkSigma : .{P : a -> Type} -> (x : a) -> (pf : P x) -> Sigma a P



                                                                                                                          



