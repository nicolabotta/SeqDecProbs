> module Ops

Basic propositional connectives at |Type|-level instead of |Bool|.

> Not           :  (A : Type) -> Type
> Not A         =  A -> _|_

> or : (a -> Bool) -> (a -> Bool) -> (a -> Bool)
> or p q a = p a || q a