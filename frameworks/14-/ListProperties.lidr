> module ListProperties

> import Data.List
> import Syntax.PreorderReasoning

> import FunOperations

> %default total
> %auto_implicits off
> %access public export


> ||| 
> mapSndMapCrossAnyIdLemma : {A, B, C : Type} -> 
>                            (f : A -> C) -> 
>                            (abs : List (A, B)) -> 
>                            map snd (map (cross f id) abs) = map snd abs
> mapSndMapCrossAnyIdLemma _ Nil = Refl
> mapSndMapCrossAnyIdLemma f ((a, b) :: abs) = 
>     ( map snd (map (cross f id) ((a, b) :: abs)) )
>   ={ Refl }=
>     ( map snd ((f a, b) :: map (cross f id) abs) )
>   ={ Refl }=
>     ( b :: map snd (map (cross f id) abs) )
>   ={ cong (mapSndMapCrossAnyIdLemma f abs) }=
>     ( b :: map snd abs )
>   ={ Refl }=
>     ( map snd ((a, b) :: abs) )
>   QED
> %freeze mapSndMapCrossAnyIdLemma
