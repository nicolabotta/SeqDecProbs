> module Finite

> import Data.Fin
> import Control.Isomorphism


> %default total 


> ||| Notion of finiteness for types
> Finite : Type -> Type
> Finite A = Exists (\ n => Iso A (Fin n))


