> module SoProperties


> import Data.So

> import Decidable
> import Prop


> %default total 


Decidability

> ||| Lifted Booleans are decidable
> decSo : (b : Bool) -> Dec (So b) 
> decSo True  = Yes Oh 
> decSo False = No (\ oh => absurd oh) 


> ||| Lifted Boolean functions are decidable
> dec1So : {A : Type} -> (p : A -> Bool) -> Dec1 (\ a => So (p a)) 
> dec1So p a = decSo (p a)
