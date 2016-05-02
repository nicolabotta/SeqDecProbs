> module SeqDecProbsUtils

> import Data.Fin
> import Control.Isomorphism

> import SeqDecProbsCoreAssumptions
> import SeqDecProbsCoreTheory
> import Sigma
> import SigmaOperations
> import Finite

> %default total
> %access public export
> %auto_implicits on


* ...

> |||
> FiniteViable : Type
> FiniteViable = {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Viable {t} n x)

> |||
> FiniteAll : Type
> FiniteAll = {A : Type} -> {P : A -> Type} -> Finite1 P -> (ma : M A) -> Finite (All P ma)

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
> FiniteGoodCtrl : Type
> FiniteGoodCtrl = {t : Nat} -> {n : Nat} -> 
>                  (x : State t) -> Viable {t = t} (S n) x ->
>                  Finite (GoodCtrl t x n) 

> finiteAllViable : FiniteAll -> FiniteViable -> FiniteAllViable
> finiteAllViable fAll fViable = fAllViable where
>   fAll' : {A : Type} -> {P : A -> Type} -> Finite1 P -> (ma : M A) -> Finite (All P ma)
>   fAll' = fAll
>   fViable' : {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Viable {t} n x)
>   fViable' = fViable
>   fAllViable : {t : Nat} -> {n : Nat} -> 
>                (x : State t) -> (y : Ctrl t x) -> 
>                Finite (All (Viable {t = S t} n) (step t x y))
>   fAllViable {t} {n} x y = fAll' (fViable' {t = S t} {n}) (step t x y)






> {-
> NonEmptyGoodCtrl : Type
> NonEmptyGoodCtrl = {t : Nat} -> {n : Nat} -> 
>                    (x : State t) -> (v : Viable {t = t} (S n) x) ->
>                    NonEmpty (fGoodCtrl {t} {n} x v)
> -}


> {-

> f1Good : {t : Nat} -> {n : Nat} -> 
>          (x : State t) -> Finite1 (Good t x n)
> f1Good {t} {n} x y = finiteAll (fViable {t = S t} {n}) (step t x y)

> finiteGoodCtrl : {t : Nat} -> {n : Nat} ->
>                  (fViable : (x' : State (S t)) -> Finite (Viable {t = S t} n x')) ->
>                   
>                  (x : State t) -> Viable {t = t} (S n) x ->
>                  Finite (GoodCtrl t x n) 
> finiteGoodCtrl {t} {n} x v = finiteSigmaLemma0 (fCtrl {t} {x}) (f1Good {t} {n} x)

> -}


* Show states and controls

> |||
> showState : {t : Nat} -> State t -> String

> |||
> showCtrl : {t : Nat} -> {x : State t} -> Ctrl t x -> String

> |||
> showStateCtrl : {t : Nat} -> Sigma (State t) (Ctrl t) -> String
> showStateCtrl {t} (MkSigma x y) = "(" ++ showState {t} x ++ " ** " ++ showCtrl {t} {x} y ++ ")"


* Sequences of state-control pairs

> ||| 
> data StateCtrlSeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  {t : Nat} -> 
>            (x : State t) -> StateCtrlSeq t Z
>   (::)  :  {t : Nat} -> {n : Nat} -> 
>            Sigma (State t) (Ctrl t) -> StateCtrlSeq (S t) n -> StateCtrlSeq t (S n)

> using (t : Nat, n : Nat)
>   implementation Show (StateCtrlSeq t n) where
>     show = show' where
>       show' : {t : Nat} -> {n : Nat} -> StateCtrlSeq t n -> String
>       show' xys = "[" ++ show'' "" xys ++ "]" where
>         show'' : {t' : Nat} -> {n' : Nat} -> String -> StateCtrlSeq t' n' -> String
>         show'' {t'} {n' =   Z}      acc (Nil x)      =
>           acc ++ "(" ++ showState x ++ " ** " ++ " " ++ ")" 
>         show'' {t'} {n' = S m'} acc (xy :: xys)    = 
>           show'' {t' = S t'} {n' = m'} (acc ++ showStateCtrl xy ++ ", ") xys


* Trajectories

> |||
> stateCtrlTrj : {t : Nat} -> {n : Nat} -> 
>                (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>                (ps : PolicySeq t n) -> M (StateCtrlSeq t n)
> stateCtrlTrj {t} {n = Z}   x r v Nil = ret (Nil x)
> stateCtrlTrj {t} {n = S m} x r v (p :: ps') =
>   fmap g (bind (tagElem mx') f) where
>     y : Ctrl t x
>     y = ctrl (p x r v)
>     mx' : M (State (S t))
>     mx' = step t x y
>     av  : All (Viable m) mx'
>     av  = allViable {y = y} (p x r v)
>     g : StateCtrlSeq (S t) m -> StateCtrlSeq t (S m)
>     g = ((MkSigma x y) ::)
>     f : Sigma (State (S t)) (\ x' => x' `Elem` mx') -> M (StateCtrlSeq (S t) m)
>     f (MkSigma x' x'estep) = stateCtrlTrj {n = m} x' r' v' ps' where
>       ar : All Reachable (step t x y)
>       ar = reachableSpec1 x r y
>       r' : Reachable x'
>       r' = containerMonadSpec3 x' (step t x y) ar x'estep
>       v' : Viable m x'
>       v' = containerMonadSpec3 x' (step t x y) av x'estep


