> import Data.Vect
> import Data.Fin
> %default total


Injectivity: the idea is that any vector |as : Vect n A| can be seen as
a function of type |Fin n -> A|

> asFunction : {A : Type} -> {n : Nat} -> Vect n A -> Fin n -> A
> asFunction = flip index

Thus, it is natural to say that |as| is injective if |asFunction as| is
injective. We have two notions of injectivity for functions:

> Injective1 : {A, B : Type} -> (f : A -> B) -> Type
> Injective1 {A} f = (a1 : A) -> (a2 : A) -> f a1 = f a2 -> a1 = a2

> Injective2 : {A, B : Type} -> (f : A -> B) -> Type
> Injective2 {A} f = (a1 : A) -> (a2 : A) -> Not (a1 = a2) -> Not (f a1 = f a2)

with

> injectiveLemma : {A, B : Type} -> (f : A -> B) -> Injective1 f -> Injective2 f
> injectiveLemma f i1f a1 a2 contra = contra . (i1f a1 a2) 

and we can extend these notions to vectors:

> namespace Vect

>   Injective1 : {A : Type} -> {n : Nat} -> Vect n A -> Type
>   Injective1 = Injective1 . asFunction

>   Injective2 : {A : Type} -> {n : Nat} -> Vect n A -> Type
>   Injective2 = Injective2 . asFunction

>   injectiveLemma : {A : Type} -> {n : Nat} -> 
>                    (as : Vect n A) -> Vect.Injective1 as -> Vect.Injective2 as
>   injectiveLemma as ias = injectiveLemma (asFunction as) ias  


Operations on vectors that simply discard certain elements should
preserve injectivity. For instance, taking the tail of a vector
preserves injectivity

> injectiveTailLemma1 : (xs : Vect (S n) t) -> Injective1 xs -> Injective1 (tail xs)
> injectiveTailLemma1  Nil      p _ _ _ impossible
> injectiveTailLemma1 (x :: xs) p i j q = FSInjective i j (p (FS i) (FS j) q') where
>   q' : index (FS i) (x :: xs) = index (FS j) (x :: xs)
>   q' = q

filtering a vector with a decidable property

> Dec1 : {A : Type} -> (P : A -> Type) -> Type
> Dec1 {A} P = (a : A) -> Dec (P a) 

> filterDec : {A : Type} -> {n : Nat} -> {P : A -> Type} ->
>             Dec1 P -> Vect n A -> Sigma Nat (\m => Vect m A)
> filterDec dP Nil = (Z ** Nil)
> filterDec dP (a :: as) with (filterDec dP as)
>   | (n ** as') with (dP a)
>     | (Yes _) = (S n ** a :: as')
>     | (No  _) = (n ** as')

should also preserve injectivity

> filterDec1 : {A : Type} -> {n : Nat} -> {P : A -> Type} ->
>              Dec1 P -> Vect n A -> Nat
> filterDec1 dP as = getWitness (filterDec dP as)

> filterDec2 : {A : Type} -> {n : Nat} -> {P : A -> Type} ->
>              (dP : Dec1 P) -> (as : Vect n A) -> Vect (filterDec1 dP as) A
> filterDec2 dP as = getProof (filterDec dP as)

> injectiveFilterDecLemma : 
>   {A : Type} -> {P : A -> Type} -> {n : Nat} ->
>   (dP : Dec1 P) -> (as : Vect n A) ->
>   Injective1 as -> Injective1 (filterDec2 dP as)

It turns out that a direct proof of |injectiveFilterDecLemma| is
awkward. 

...

Matteo has suggested a more elegant approach. The idea (if I have
understood it correctly) is to give inductive notions of the property of
having no duplicates

> namespace NotElem

>   data NotElem : {A : Type} -> {n : Nat} -> A -> Vect n A -> Type where
>     Nil  : {A : Type} -> {x : A} -> 
>            NotElem {A = A} {n = Z} x Nil
>     (::) : {A : Type} -> {n : Nat} -> {x, y : A} -> {xs : Vect n A} -> 
>            Not (x = y) -> NotElem x xs -> NotElem x (y :: xs) 

> namespace NoDups

>   data NoDups : Vect n t -> Type where
>     Nil  : NoDups Nil
>     (::) : NotElem x xs -> NoDups xs -> NoDups (x :: xs) 

, prove that filtering does not introduce duplicates

> noDupsFilterDecLemma : 
>   {A : Type} -> {P : A -> Type} -> {n : Nat} ->
>   (dP : Dec1 P) -> (as : Vect n A) ->
>   NoDups as -> NoDups (filterDec2 dP as)

and finally show that having no duplicates and being injective are equivalent

> noDupsInjective1Lemma : 
>   {A : Type} -> {n : Nat} ->
>   (as : Vect n A) -> NoDups as -> Injective1 as

> injective1NoDupsLemma : 
>   {A : Type} -> {n : Nat} ->
>   (as : Vect n A) -> Injective1 as -> NoDups as

With |noDupsFilterDecLemma|, |noDupsInjective1Lemma| and
|injective1NoDupsLemma| in place, one can implement
|injectiveFilterDecLemma| straightforwardly:

> injectiveFilterDecLemma {A} {n} {P} dP as ias = 
>   noDupsInjective1Lemma fas ndfas where
>     ndas  : NoDups as
>     ndas  = injective1NoDupsLemma as ias
>     m     : Nat
>     m     = filterDec1 dP as
>     fas   : Vect m A
>     fas   = filterDec2 dP as 
>     ndfas : NoDups fas
>     ndfas = noDupsFilterDecLemma dP as ndas

Thus, the question is whether one can implement |noDupsFilterDecLemma|,
|noDupsInjective1Lemma| and |injective1NoDupsLemma|. 

> --noDupsFilterDecLemma : 
> --  {A : Type} -> {P : A -> Type} -> {n : Nat} ->
> --  (dP : Dec1 P) -> (as : Vect n A) ->
> --  NoDups as -> NoDups (filterDec2 dP as)
> noDupsFilterDecLemma dP  Nil      ndNil = Nil
> noDupsFilterDecLemma dP (a :: as) (neaas :: ndas) with (filterDec dP as) proof itsEqual
>   | (n ** fas) with (dP a) 
>     | (Yes _) = ?lika
>     | (No  _) = replace {P = \ rec => NoDups (getProof rec)} (sym itsEqual) (noDupsFilterDecLemma dP as ndas)


filterDec-NoDups : ∀ {n}{xs : Vec A n} → NoDups xs → NoDups (filterDec₂ dec xs)
filterDec-NoDups [] = []
filterDec-NoDups (_∷_ {x = x} a ns) with dec x
filterDec-NoDups (_∷_ n ns) | yes p = filterDec-□ n ∷ filterDec-NoDups ns
filterDec-NoDups (_∷_ n ns) | no ¬p = filterDec-NoDups ns



> namespace All

>   data All : {A : Type} -> {n : Nat} ->
>              (P : A -> Type) -> (xs : Vect n A) -> Type where 
>     Nil  : {A : Type} -> {P : A -> Type} -> All P Nil
>     (::) : {A : Type} -> {n : Nat} -> {P : A -> Type} -> {x : A} -> {xs : Vect n A} -> 
>            P x -> All P xs -> All P (x :: xs)





> AllNotElemLemma1 : NotElem x xs -> All (\ y => Not (y = x)) xs






   
   
