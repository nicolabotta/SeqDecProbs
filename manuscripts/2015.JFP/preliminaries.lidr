> namespace Nat
>   %hide Nat
>   %hide Z
>   %hide S
>
>   data Nat : Type where
>     Z  : Nat
>     S  : Nat -> Nat
>
> data Vect : Nat -> Type -> Type where
>   Nil   :  Vect Z a
>   Cons  :  (x : a) -> (xs : Vect n a) -> Vect (S n) a
>
> head : {n : Nat} -> {A : Type} -> Vect (S n) A -> A
> head (Cons x xs) = x
>
> postulate A       : Type
> postulate Sorted  : Vect n A -> Type
> postulate sort    : Vect n A -> Vect n A
>
> SortSpec : Type      -- a specificatation of |sort|
> SortSpec = (n : Nat) -> (xs : Vect n A) -> Sorted (sort xs)
>
> sortLemma : SortSpec
> sortLemma = ?hole {- a proof that |sort| satisfies the specification -}
>
> namespace Existential
>   %hide Prelude.Pairs.Exists
>   using (A : Type, P : A -> Type)
>     data Exists : {A : Type} -> (A -> Type) -> Type where
>       Evidence : (wit : A) -> (pro : P wit) -> Exists P
>
>     getWitness  :  Exists {A} P          ->  A
>     getWitness     (Evidence wit pro)    =   wit
>
>     getProof    :  (evi : Exists {A} P)  ->  P (getWitness evi)
>     getProof       (Evidence wit pro)    =   pro
>
> data Sigma :  (A : Type) -> (A -> Type) -> Type where
>   MkSigma  :  {A : Type} -> {B : A -> Type} ->
>               (a : A) -> (b : B a) -> Sigma A B
