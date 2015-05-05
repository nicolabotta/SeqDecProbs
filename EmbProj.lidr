> module EmbProj

> import Syntax.PreorderReasoning
> import Prop

> record EmbProj : Type -> Type -> Type where
>   MkEmbProj : {A : Type} -> {B : Type} ->
>               (to : A -> B) ->
>               (from : B -> Maybe A) ->
>               (fromTo : (x : A) -> from (to x) = Just x) ->
>               EmbProj A B

> epRefl : {A : Type} -> EmbProj A A
> epRefl = MkEmbProj id Just (\x => Refl)

> IsInjective : {A : Type} -> {B : Type} -> (to : A -> B) -> Prop
> IsInjective {A} {B} to = (x1, x2 : A) -> (to x1 = to x2) -> (x1 = x2)

> EmbProjIsInjective : (ep : EmbProj a b) -> IsInjective (to ep)
> EmbProjIsInjective (MkEmbProj to from fromTo) x1 x2 p =
>   justInjective ((Just x1)       ={ sym (fromTo x1) }=
>                  (from (to x1))  ={ cong p }=
>                  (from (to x2))  ={ fromTo x2 }=
>                  (Just x2)
>                  QED)


> ||| Just is injective
> total justInjective : {x : a} -> {y : a} -> (Just x = Just y) -> (x = y)
> justInjective Refl = Refl

> -- Alternative definition:
> justIsInjective2 : IsInjective Just
> justIsInjective2 _ _ Refl = Refl
