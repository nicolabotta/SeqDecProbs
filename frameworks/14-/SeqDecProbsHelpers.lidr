> module SeqDecProbsHelpers

> import Data.Fin
> import Control.Isomorphism

> import SeqDecProbsCoreAssumptions
> import SeqDecProbsCoreTheory
> import Finite
> import FiniteOperations
> import FiniteProperties
> import Sigma
> import SigmaOperations
> import SigmaProperties

> %default total
> %access public export
> %auto_implicits off


* Finiteness notions

> |||
> FiniteViable : Type
> FiniteViable = {t : Nat} -> {n : Nat} -> 
>                (x : State t) -> Finite (Viable {t} n x)

> |||
> FiniteAll : Type
> FiniteAll = {A : Type} -> {P : A -> Type} -> 
>             Finite1 P -> (ma : M A) -> Finite (All P ma)

> |||
> FiniteAllViable : Type
> FiniteAllViable = {t : Nat} -> {n : Nat} -> 
>                   (x : State t) -> (y : Ctrl t x) -> 
>                   Finite (All (Viable {t = S t} n) (step t x y))

> |||
> FiniteNonEmpty : Type
> FiniteNonEmpty = {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> (y : Ctrl t x) -> 
>                  Finite (SeqDecProbsCoreAssumptions.NonEmpty (step t x y))

> |||
> FiniteGood : Type
> FiniteGood = {t : Nat} -> {n : Nat} -> 
>              (x : State t) -> (y : Ctrl t x) -> 
>              Finite (Good t x n y)

> |||
> FiniteCtrl : Type
> FiniteCtrl = {t : Nat} -> {n : Nat} -> 
>              (x : State t) -> Finite (Ctrl t x) 

> |||
> FiniteGoodCtrl : Type
> FiniteGoodCtrl = {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> Viable {t = t} (S n) x ->
>                  Finite (GoodCtrl t x n) 


* Standard deduction patterns in the implementation of specific SDPs

We would like to provide users with a function

< finiteAllViable : FiniteAll -> FiniteViable -> FiniteAllViable

but, as it turns out, implementing this function is not trivial (see
issues 3135 and 3136). Thus, for the time being, we introduce 2
additional assumptions in the global context

> ||| If users can prove that All is finite ... 
> finiteAll : {A : Type} -> {P : A -> Type} -> 
>             Finite1 P -> (ma : M A) -> Finite (All P ma)

> ||| ... and that Viable is finite,
> finiteViable : {t : Nat} -> {n : Nat} -> 
>                (x : State t) -> Finite (Viable {t} n x)

and apply them to deduce finiteness of |All Viable|.

> ||| we can deduce that All Viable is finite
> finiteAllViable : {t : Nat} -> {n : Nat} -> 
>                   (x : State t) -> (y : Ctrl t x) -> 
>                   Finite (All (Viable {t = S t} n) (step t x y))
> finiteAllViable {t} {n} x y = finiteAll (finiteViable {t = S t} {n}) (step t x y)


Similarly, we assume that users are able to prove that |NonEmpty| is finite

> finiteNonEmpty : {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> (y : Ctrl t x) -> 
>                  Finite (SeqDecProbsCoreAssumptions.NonEmpty (step t x y))

Finiteness of |NonEmpty| and |All Viable| directly implies finiteness of
|Good|

> |||
> finiteGood : {t : Nat} -> {n : Nat} -> 
>              (x : State t) -> (y : Ctrl t x) -> 
>              Finite (Good t x n y)
> finiteGood {n} x y = finiteProduct (finiteNonEmpty {n} x y) (finiteAllViable x y)
> -- finiteGood {n} x y = finiteAllViable x y

and, assuming finiteness of controls, finiteness of |GoodCtrl|:

> |||
> finiteCtrl : {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Ctrl t x) 

> ||| 
> finiteGoodCtrl : {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> 
>                  Finite (GoodCtrl t x n) 
> finiteGoodCtrl {t} {n} x = finiteSigmaLemma0 (finiteCtrl {t} {n} x) (finiteGood {t} {n} x)

Finally, we can show

> |||
> cardNotZGoodCtrl : {t : Nat} -> {n : Nat} -> 
>                    (x : State t) -> (v : Viable {t = t} (S n) x) ->
>                    CardNotZ (finiteGoodCtrl {t} {n} x)
> cardNotZGoodCtrl x v = cardNotZLemma (finiteGoodCtrl x) (viableSpec1 x v)


> {-
 
> ---}
 
