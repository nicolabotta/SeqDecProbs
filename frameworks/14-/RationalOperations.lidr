> module RationalOperations

> import Data.Sign
> import Syntax.PreorderReasoning

> import RationalSpecification


> %default total


Constants:

> zeroQ : Q
> zeroQ = fromIntegerQ 0

> oneQ : Q
> oneQ = fromIntegerQ 1


Operations

> |||
> neg : Q -> Q

> negSpec0 : (q : Q) -> sign q = Zero -> sign (neg q) = Zero
> negSpec1 : (q : Q) -> sign q = Minus -> sign (neg q) = Plus
> negSpec2 : (q : Q) -> sign q = Plus -> sign (neg q) = Minus

> |||
> plus  : Q -> Q -> Q

> |||
> minus : Q -> Q -> Q

> |||
> mult  : Q -> Q -> Q

