> module NatProperties


> %default total


> instance Uninhabited (LTE (S n) Z) where
>   uninhabited LTEZero impossible
>   uninhabited (LTESucc x) impossible

