> module SeqDecProbsCoreUtils

> import SeqDecProbsCoreAssumptions
> import SeqDecProbsCoreTheory
> import Sigma
> import SigmaOperations

> %default total
> %access public export
> %auto_implicits off


* Show states and controls

> |||
> showState : {t : Nat} -> State t -> String

> |||
> showCtrl : {t : Nat} -> {x : State t} -> Ctrl t x -> String

> |||
> showStateCtrl : {t : Nat} -> Sigma (State t) (Ctrl t) -> String
> showStateCtrl {t} (MkSigma x y) = "(" ++ showState {t} x ++ " ** " ++ showCtrl {t} {x} y ++ ")"


> ||| 
> data StateCtrlSeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  {t : Nat} -> 
>            (x : State t) -> StateCtrlSeq t Z
>   (::)  :  {t : Nat} -> {n : Nat} -> 
>            Sigma (State t) (Ctrl t) -> StateCtrlSeq (S t) n -> StateCtrlSeq t (S n)


> |||
> stateCtrlTrj : {t : Nat} -> {n : Nat} -> 
>                (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>                (ps : PolicySeq t n) -> M (StateCtrlSeq t n)
> stateCtrlTrj {t} {n = Z}   x r v Nil = ret (Nil x)
> stateCtrlTrj {t} {n = S m} x r v (p :: ps') =
>   fmap g (bind (tagElem mx') f) where
>     y : Ctrl t x
>     y = outl (p x r v)
>     mx' : M (State (S t))
>     mx' = step t x y
>     av  : All (Viable m) mx'
>     av  = outr (p x r v)
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
