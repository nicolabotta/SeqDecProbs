> module SeqDecProbMonadicUtils

> import SeqDecProbMonadicTheory
> import Sigma


> %default total
> %access public export
> %auto_implicits off


> |||
> showState : {t : Nat} -> X t -> String


> |||
> showCtrl : {t : Nat} -> {x : X t} -> Y t x -> String


> |||
> showStateCtrl : {t : Nat} -> Sigma (X t) (Y t) -> String
> showStateCtrl {t} (MkSigma x y) = "(" ++ showState {t} x ++ " ** " ++ showCtrl {t} {x} y ++ ")"



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
