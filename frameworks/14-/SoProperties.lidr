> module SoProperties


> import Data.So

> import Prop
> import Decidable
> import Unique


> %default total
> %access public export
> %auto_implicits on


Introduction and elimination rules

> |||
> soIntro : (b : Bool) -> b = True -> So b
> soIntro True  Refl   = Oh
> soIntro False contra = void (trueNotFalse (sym contra))
> %freeze soIntro 


> |||
> soOrIntro1 : (b1 : Bool) -> (b2 : Bool) -> So b1 -> So (b1 || b2)
> soOrIntro1 True _  Oh = Oh
> %freeze soOrIntro1


> |||
> soOrIntro2 : (b1 : Bool) -> (b2 : Bool) -> So b2 -> So (b1 || b2)
> soOrIntro2 True  True Oh = Oh
> soOrIntro2 False True Oh = Oh
> %freeze soOrIntro2


> |||
> soOrElim : (b1 : Bool) -> (b2 : Bool) -> So (b1 || b2) -> Either (So b1) (So b2)
> soOrElim True  True  Oh = Left Oh
> soOrElim True  False Oh = Left Oh
> soOrElim False True  Oh = Right Oh
> soOrElim False False Oh impossible
> %freeze soOrElim


> |||
> soOrElim1 : (b1 : Bool) -> (b2 : Bool) -> So (b1 || b2) -> So (not b1) -> So b2
> soOrElim1 True  True  Oh Oh impossible
> soOrElim1 True  False Oh Oh impossible
> soOrElim1 False True  Oh Oh = Oh
> soOrElim1 False False Oh Oh impossible
> %freeze soOrElim1


> |||
> soOrElim2 : (b1 : Bool) -> (b2 : Bool) -> So (b1 || b2) -> So (not b2) -> So b1
> soOrElim2 True  True  Oh Oh impossible
> soOrElim2 True  False Oh Oh = Oh
> soOrElim2 False True  Oh Oh impossible
> soOrElim2 False False Oh Oh impossible
> %freeze soOrElim2


Decidability

> ||| Lifted Booleans are decidable
> decSo : (b : Bool) -> Dec (So b)
> decSo True  = Yes Oh
> decSo False = No (\ oh => absurd oh)
> %freeze decSo


> ||| Lifted Boolean functions are decidable
> dec1So : {A : Type} -> (p : A -> Bool) -> Dec1 (\ a => So (p a))
> dec1So p a = decSo (p a)
> %freeze dec1So


Uniqueness

> ||| Lifted Booleans are unique
> %assert_total
> uniqueSo : (b : Bool) -> Unique (So b)
> uniqueSo True  Oh Oh = Refl
> uniqueSo False Oh Oh impossible
> %freeze uniqueSo


> ||| Lifted Boolean functions are unique
> unique1So : {A : Type} -> (p : A -> Bool) -> Unique1 (\ a => So (p a))
> unique1So p a = uniqueSo (p a)
> %freeze unique1So


> {-

> ---}
