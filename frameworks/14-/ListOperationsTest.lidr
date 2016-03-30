> module ListOperationsTest

> import Data.List

> import ListOperations
> import Sigma

> %default total
> %access public export
> %auto_implicits off


> xs : List Nat
> xs = [0,3,2]

> txs : List (Sigma Nat (\ n => n `Elem` xs))
> txs = tagElem xs
