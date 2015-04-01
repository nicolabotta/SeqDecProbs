> module TestExists

> A : Type

> P : A -> Type

> astpa : (a : A ** P a)

> astpa' : Exists A P
> astpa' = astpa