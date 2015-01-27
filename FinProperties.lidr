> module FinProperties

> import Data.Fin
 

> %default total


> finToNatLemma : (k : Fin n) -> LT (finToNat k) n 
> finToNatLemma {n = Z}   k       =  absurd k
> finToNatLemma {n = S m} FZ      =  LTESucc LTEZero 
> finToNatLemma {n = S m} (FS k)  =  LTESucc (finToNatLemma k) 
