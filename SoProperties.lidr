> module SoProperties


> import Data.So

> import Decidable
> import Prop


> %default total 


Introduction and elimination rules

> |||
> soOrIntro1 : (b1 : Bool) -> (b2 : Bool) -> So b1 -> So (b1 || b2)
> soOrIntro1 True _  Oh = Oh 


> |||
> soOrIntro2 : (b1 : Bool) -> (b2 : Bool) -> So b2 -> So (b1 || b2)
> soOrIntro2 True  True Oh = Oh 
> soOrIntro2 False True Oh = Oh 


Decidability

> ||| Lifted Booleans are decidable
> decSo : (b : Bool) -> Dec (So b) 
> decSo True  = Yes Oh 
> decSo False = No (\ oh => absurd oh) 


> ||| Lifted Boolean functions are decidable
> dec1So : {A : Type} -> (p : A -> Bool) -> Dec1 (\ a => So (p a)) 
> dec1So p a = decSo (p a)
