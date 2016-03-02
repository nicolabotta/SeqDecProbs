> module ListProperties

> import Data.List
> import Data.List.Quantifiers
> import Syntax.PreorderReasoning

> import FunOperations

> %default total
> %auto_implicits off
> %access public export


|List| is a functor:

> -- functorSpec1 : fmap . id = id

> -- functorSpec2 : fmap (f . g) = (fmap f) . (fmap g)


|List| is a monad:

> -- monadSpec1 : (fmap f) . ret = ret . f

> -- monadSpec21 : bind (ret a) f = f a

> -- monadSpec22 : bind ma ret = ma

> -- monadSpec23 : {A, B, C : Type} -> {f : A -> M B} -> {g : B -> M C} ->
> --                bind (bind ma f) g = bind ma (\ a => bind (f a) g)


|List| is a container monad:

> -- containerMonadSpec1 : a `Elem` (ret a)

> -- containerMonadSpec2 : {A : Type} -> (a : A) -> (ma : M A) -> (mma : M (M A)) ->
> --                       a `Elem` ma -> ma `Elem` mma -> a `Elem` (join mma)

> containerMonadSpec3 : {A : Type} -> {P : A -> Type} -> (a : A) -> (as : List A) ->
>                       All P as -> a `Elem` as -> P a
> containerMonadSpec3 a'  Nil       _           eprf        = absurd eprf
> containerMonadSpec3 a  (a :: as) (pa :: pas)  Here        = pa
> containerMonadSpec3 a' (a :: as) (pa :: pas) (There eprf) = containerMonadSpec3 a' as pas eprf
> %freeze containerMonadSpec3

> -- containerMonadSpec4 : {A : Type} -> (ma : M A) -> fmap outl (tagElem ma) = ma


Fusion-related properties:

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



