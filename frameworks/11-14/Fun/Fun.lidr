> module Fun

> {-
> HasUnitSumOn : (Functor t, Foldable t, Num b) => (f : a -> b) -> (ta : t a) -> Type
> HasUnitSumOn f ta = sum (map f ta) = 1
> -}

> HasUnitSumOn : (Functor t, Foldable t) => (f : a -> Float) -> (ta : t a) -> Type
> HasUnitSumOn f ta = sum (map f ta) = 1

