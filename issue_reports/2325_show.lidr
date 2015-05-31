> import Data.Vect

> data Action = Do | Undo

> instance Show Action where
>   show Do = "Do"
>   show Undo = "Undo"
