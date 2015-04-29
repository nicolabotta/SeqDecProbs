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
awkward. You can find an attempt at a direct proof in

https://github.com/nicolabotta/SeqDecProbs/blob/master/idris-lang/injective_filter_lemma.3.lidr

The code type checks but is incomplete. Also, it is ugly (look at the
extensive usage of |replace| in the computation of |s9| at lines
80-120!). I am probably missing something obvious but I have not managed
to come up wiht a clean direct proof.

Matteo has suggested a more elegant approach. The idea is, if I have
understood it correctly, to give inductive definitions of the property
of having no duplicates

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
|noDupsInjective1Lemma| and |injective1NoDupsLemma|. It is easy to
implement |noDupsFilterDecLemma| if one can show

> notElemFilterDecLemma : 
>   {A : Type} -> {P : A -> Type} -> {n : Nat} -> 
>   (a : A) -> (as : Vect n A) -> (dP : Dec1 P) ->
>   NotElem a as -> NotElem a (filterDec2 dP as)

Then

> noDupsFilterDecLemma dP  Nil      ndNil = Nil
> noDupsFilterDecLemma dP (a :: as) (neaas :: ndas) with (filterDec dP as) proof itsEqual
>   | (n ** fas) with (dP a) 
>     | (Yes _) = neafas :: ndfas where
>       neafas : NotElem a fas 
>       neafas = replace {P = \ rec => NotElem a (getProof rec)} (sym itsEqual) (notElemFilterDecLemma a as dP neaas)
>       ndfas  : NoDups fas
>       ndfas  = replace {P = \ rec => NoDups (getProof rec)} (sym itsEqual) (noDupsFilterDecLemma dP as ndas)
>     | (No  _) = replace {P = \ rec => NoDups (getProof rec)} (sym itsEqual) (noDupsFilterDecLemma dP as ndas)

Thus, we are left with the problem of proving |notElemFilterDecLemma|,
|noDupsInjective1Lemma| and |injective1NoDupsLemma|. Matteo has
recognized that |notElemFilterDecLemma| is a special case of a more
general lemma:

> namespace All

>   data All : {A : Type} -> {n : Nat} ->
>              (P : A -> Type) -> (xs : Vect n A) -> Type where 
>     Nil  : {A : Type} -> {P : A -> Type} -> All P Nil
>     (::) : {A : Type} -> {n : Nat} -> {P : A -> Type} -> {x : A} -> {xs : Vect n A} -> 
>            P x -> All P xs -> All P (x :: xs)

> allFilterDecLemma : 
>   {A : Type} -> {n : Nat} -> 
>   (P1 : A -> Type) -> (P2 : A -> Type) -> (dP2 : Dec1 P2) -> (as : Vect n A) ->
>   All P1 as -> All P1 (filterDec2 dP2 as)
> allFilterDecLemma P1 P2 dP2  Nil             allas  = Nil
> allFilterDecLemma P1 P2 dP2 (a :: as) (pa :: allas) with (filterDec dP2 as) proof itsEqual
>   | (n ** fas) with (dP2 a) 
>     | (Yes _) = pa :: allfas where
>       allfas : All P1 fas 
>       allfas = replace {P = \ rec => All P1 (getProof rec)} (sym itsEqual) (allFilterDecLemma P1 P2 dP2 as allas)
>     | (No  _) = replace {P = \ rec => All P1 (getProof rec)} (sym itsEqual) (allFilterDecLemma P1 P2 dP2 as allas)

since |NotElem a as| can be inferred from |All (\ a' => Not (a' = a)) as|:

> allNotElemLemma : 
>   {A : Type} -> {n : Nat} -> 
>   (a : A) -> (as : Vect n A) -> All (\ a' => Not (a = a')) as -> NotElem a as
> allNotElemLemma a  Nil        prf             = Nil
> allNotElemLemma a (a' :: as) (naeqa' :: prf') = neaa'as where
>   neaas   : NotElem a as
>   neaas   = allNotElemLemma a as prf'
>   neaa'as : NotElem a (a' :: as)
>   neaa'as = naeqa' :: neaas

and the other way round

> notElemAllLemma : 
>   {A : Type} -> {n : Nat} -> 
>   (a : A) -> (as : Vect n A) -> NotElem a as -> All (\ a' => Not (a = a')) as
> notElemAllLemma a  Nil       prf = Nil
> notElemAllLemma a (a' :: as) (naeqa' :: neaas) = (naeqa' :: allas) where
>   allas : All (\ a' => Not (a = a')) as
>   allas = notElemAllLemma a as neaas

and therefore

> notElemFilterDecLemma {A} {P} {n} a as dP neaas = neafas where
>   P1 : A -> Type
>   P1 = \ a' => Not (a = a')
>   allas  : All P1 as
>   allas  = notElemAllLemma a as neaas
>   allfas : All P1 (filterDec2 dP as)
>   allfas = allFilterDecLemma P1 P dP as allas
>   neafas : NotElem a (filterDec2 dP as)
>   neafas = allNotElemLemma a (filterDec2 dP as) allfas

In fact, Matteo has shown a more interesting result: namely that both
|allFilterDecLemma| and |noDupsFilterDecLemma| can be derived from a
more general property:

> namespace DeepAll

>   data DeepAll : {A : Type} -> {n : Nat} -> 
>                  (P : (m : Nat) -> A -> Vect m A -> Type) -> Vect n A -> Type where 
>     Nil  : {A : Type} -> {P : (m : Nat) -> A -> Vect m A -> Type} -> 
>            DeepAll {A} {n = Z} P Nil
>     (::) : {A : Type} -> {n : Nat} -> {P : (m : Nat) -> A -> Vect m A -> Type} -> 
>            {a : A} -> {as : Vect n A} -> 
>            P n a as -> DeepAll P as -> DeepAll P (a :: as)

< deepAllFilterDecLemma : 
<   {A : Type} -> {n : Nat} -> 
<   (P1 : (m : Nat) -> A -> Vect m A -> Type) -> (P2 : A -> Type) -> (dP2 : Dec1 P2) -> (a : A) -> (as : Vect n A) ->
<   P1 n a as -> 
<   P1 (filterDec1 dP2 as) a (filterDec2 dP2 as) -> 
<   DeepAll P1 as -> 
<   DeepAll P1 (filterDec2 dP2 as)

...

No matter how |allFilterDecLemma| and |noDupsFilterDecLemma| are
derived, we are left with two proof obligations: |noDupsInjective1Lemma|
and |injective1NoDupsLemma|. Following Matteo's derivation ...








   
   
