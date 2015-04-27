I am trying to prove that filtering a vector with a decidable property

> import Data.Vect
> import Data.Fin
> %default total

> Dec1 : {A : Type} -> (P : A -> Type) -> Type
> Dec1 {A} P = (a : A) -> Dec (P a) 

> filterDec : {A : Type} -> {P : A -> Type} ->
>             Dec1 P -> Vect n A -> Sigma Nat (\m => Vect m A)
> filterDec dP Nil = (Z ** Nil)
> filterDec dP (a :: as) with (filterDec dP as)
>   | (n ** as') with (dP a)
>     | (Yes _) = (S n ** a :: as')
>     | (No  _) = (n ** as')

does not introduce duplicates. More precisely, I would like to prove the
following lemma:

> Injective1 : Vect n t -> Type
> Injective1 {n} xs = (i : Fin n) -> (j : Fin n) -> index i xs = index j xs -> i = j

> injectiveFilterDecLemma : 
>   {A : Type} -> {P : A -> Type} -> {n : Nat} ->
>   (dP : Dec1 P) -> (as : Vect n A) ->
>   Injective1 as -> Injective1 (getProof (filterDec dP as))

I thought the proof to be almost trivial but I am stuck. I can prove
that taking the tail of a vector does not introduce duplicates:

> injectiveTailLemma1 : (xs : Vect (S n) t) -> Injective1 xs -> Injective1 (tail xs)
> injectiveTailLemma1  Nil      p _ _ _ impossible
> injectiveTailLemma1 (x :: xs) p i j q = FSInjective i j (p (FS i) (FS j) q') where
>   q' : index (FS i) (x :: xs) = index (FS j) (x :: xs)
>   q' = q

and, with some more efforts, that filtering preserves membership

> instance Uninhabited (Elem {a} x Nil) where
>   uninhabited Here impossible
>   uninhabited (There p) impossible

> filterDecLemma : 
>   {A : Type} -> {P : A -> Type} ->
>   (d1P : Dec1 P) -> (a : A) -> (as : Vect n A) ->
>   Elem a as -> (p : P a) -> Elem a (getProof (filterDec d1P as))
> filterDecLemma d1P a   Nil       prf  p = absurd prf
> filterDecLemma d1P a1 (a1 :: as) Here p with (filterDec d1P as)
>   | (n ** as') with (d1P a1)
>     | (Yes _) = Here {x = a1} {xs = as'}
>     | (No  contra) = void (contra p)
> filterDecLemma {A} {P} d1P a1 (a2 :: as) (There prf) p with (filterDec d1P as) proof itsEqual
>   | (n ** as') with (d1P a2)
>     | (Yes _) = -- There {x = a1} {xs = as'} {y = a2} (filterDecLemma d1P a1 as prf p)
>                 There {x = a1} {xs = as'} {y = a2} $
>                   replace {P = \rec => Elem a1 (getProof rec)} (sym itsEqual) $
>                     filterDecLemma {A} {P} d1P a1 as prf p
>     | (No  _) = -- filterDecLemma {A} {P} d1P a1 as prf p
>                 replace {P = \rec => Elem a1 (getProof rec)} (sym itsEqual) $
>                   filterDecLemma {P = P} d1P a1 as prf p

but I have not managed to prove |injectiveFilterDecLemma|. Does this
hold? Any idea how to implement a proof? Thanks, Nicola

PS: this file type checks with Idris 0.9.17.1-git:5cdefc5
