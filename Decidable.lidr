> module Decidable


> %default total 


> Dec1 : (p : alpha -> Type) -> Type
> Dec1 {alpha} p  =  (a : alpha) -> Dec (p a) 

