> module FooMonad
> %default total
> %auto_implicits off
> %access public export
> interface Monad m => FooMonad (m : Type -> Type) where
>   Foo : {a : Type} -> a -> m a -> Type
>   foo : {a : Type} -> (ma : m a) -> m (DPair a (\ x => Foo x ma))

