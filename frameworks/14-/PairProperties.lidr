> module PairProperties

> %default total
> %access public export
> %auto_implicits off


> pairLemma : {A, B : Type} -> (ab : (A, B)) -> ab = (fst ab, snd ab)
> pairLemma (a, b) = Refl
