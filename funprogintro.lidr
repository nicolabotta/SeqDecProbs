> import Syntax.PreorderReasoning
> 
> postulate  A : Type
> postulate  B : Type
> postulate  C : Type
> postulate  f : A -> B
> postulate  g : A -> B -> c
> postulate  x : A
> postulate  y : B

> test1 : B
> test1 = f x
> test2 : C
> test2 = (g x) y
> test3 : Int
> test3 = 2 + 3
> gx : B -> C
> gx = g x

> aNumber : Nat
> aNumber = 1738

> aFun : Nat -> Nat
> aFun = \x => 2*x+1

> aFun' : Nat -> Nat
> aFun' x = 2*x+1

> infixr 10 ^
> (^) : Float -> Nat -> Float
> x ^ Z      = 1
> x ^ (S n)  = x * (x^n)

> namespace monomorphic
>   curry : ((A, B) -> C) -> A -> B -> C
>   curry f a b = f (a, b)
>   
>   uncurry : (A -> B -> C) -> (A, B) -> C
>   uncurry f (a, b) = f a b

> discount : Float -> (Nat -> A -> Float) -> (Nat -> A -> Float)
> discount   rate     reward              =  \t =>  \x => rate^t * reward t x

> namespace polymorphic
>   curry : ((a, b) -> c) -> a -> b -> c
>   curry f a b = f (a, b)
>   
>   uncurry : (a -> b -> c) -> (a, b) -> c
>   uncurry f (a, b) = f a b

>   fst1 : (s, t) -> s
>   fst1 (x, y) = x

The type signature uses two \emph{type variables} |s| and |t| and
behind the scenes the definition is actually treated like this:

>   fst2 : {s : Type} -> {t : Type} -> (s, t) -> s
>   fst2 {s} {t} (x, y) = x

Equality and equational reasoning

> postulate unitMult   : (y : Float) -> (1*y = y)
> postulate assocMult  : (x : Float) -> (y : Float) ->  (z : Float) ->  (x*y)*z = x*(y*z)

Let's prove a lemma about exponentiation by induction over the first
|Nat| argument.
%
Then the three definitions we need to implement have the following types:

> expLemma :  (x : Float) -> (m : Nat) -> (n : Nat) -> (x^m * x^n = x^(m+n))
> baseCase :  (x : Float) -> (n : Nat) -> (x^Z * x^n = x^(Z+n))
> stepCase :  (x : Float) -> (m : Nat) -> (n : Nat) -> 
>             (ih :  x^m      * x^n = x^(m+n))      ->
>             (      x^(S m)  * x^n = x^((S m)+n))

The main lemma just uses the base case for zero and the step case for successor.
%
Note that the last argument to the step case is the induction
hypothesis: a recursive call to |expLemma|.

> expLemma x Z      n = baseCase x n
> expLemma x (S m)  n = stepCase x m n (expLemma x m n)

> baseCase x n = 
>     ( x^Z * x^n )
>   ={ Refl }=                     -- By definition of |(^)|
>     (   1 * x^n )
>   ={ unitMult (x^n) }=           -- Use |1*y=y| for |y=x^n|
>     (   x^n   )
>   ={ Refl }=                     -- By definition of |(+)|
>     ( x^(Z+n) )
>   QED

> stepCase x m n ih = 
>     ( x^(S m) * x^n      ) 
>   ={ Refl }=                     -- By definition of |(^)|
>     ( (x * x^m) * x^n    ) 
>   ={ assocMult x (x^m) (x^n) }=  -- Associativity of multiplication
>     ( x * (x^m * x^n)    )
>   ={ cong ih }=                  -- Use the induction hypothesis |expLemma x m n|
>     ( x * x^(m + n)      )
>   ={ Refl }=                     -- By definition of |(^)| (backwards)
>     ( x^(S (m + n))      )       
>   ={ Refl }=                     -- By definition of |(+)|
>     ( x^(S m + n)        )       
>   QED

> {-
> expLemma x Z      n = 
>     ( x^Z * x^n          )
>   ={ Refl }=                     -- By definition of |(^)|
>     (   1 * x^n          )
>   ={ unitMult (x^n) }=
>     (   x^n              )
>   ={ Refl }=                     -- By definition of |(+)|
>     ( x^(Z+n)            )
>   QED
> expLemma x (S m)  n = 
>     ( x^(S m) * x^n      ) 
>   ={ Refl }=                     -- By definition of |(^)|
>     ( (x * x^m) * x^n    ) 
>   ={ assocMult x (x^m) (x^n) }= 
>     ( x * (x^m * x^n)    )
>   ={ cong (expLemma x m n) }=    -- Use the induction hypothesis |expLemma x m n|
>     ( x * x^(m + n)      )
>   ={ Refl }=                     
>     ( x^(S (m + n))      )       -- By definition of |(^)| (backwards)
>   ={ Refl }=                     
>     ( x^(S m + n)        )       -- By definition of |(+)|
>   QED
> -}
 
For many examples of using the equality proof notation (in Idris'
sister language Agda), see [Algebra of Programming in Agda](http://wiki.portal.chalmers.se/cse/pmwiki.php/FP/AoPAgda).

----------------

> namespace Nat
>   %hide Nat
>   %hide Z
>   %hide S
>   
>   data Nat : Type where
>     Z  : Nat
>     S  : Nat -> Nat

> namespace Vec
>   %hide Vect
>   %hide Nil
>   data Vect : Nat -> Type -> Type where
>     Nil   : Vect Z a
>     Cons  : (x : a) -> (xs : Vect n a) -> Vect (S n) a

This declaration can be seen as an infinite family of simple datatype
declarations:

> namespace VecExpand
>   data Vect0 : Type -> Type where   Nil0  : Vect0 a
>   data Vect1 : Type -> Type where   Cons1 : (x : a) -> (xs : Vect0 a) -> Vect1 a
>   data Vect2 : Type -> Type where   Cons2 : (x : a) -> (xs : Vect1 a) -> Vect2 a

> namespace Vec
>   head : Vect (S n) A -> A
>   head (Cons x xs) = x

> namespace CurryHoward
>   Prop  : Type
>   Prop  = Type
>   FALSE : Prop
>   FALSE = Void
>   TRUE  : Prop
>   TRUE  = Unit
>   sort : Vect n A -> Vect n A
>   Sorted : Vect n A -> Prop
>   Sorted_spec : Prop
>   Sorted_spec = (n : Nat) -> (xs : Vect n A) -> Sorted (sort xs)
>   sorted_lemma : Sorted_spec
> 

Existential types

Plan: Among others, introduce the constructors of existential types
(|Evidence|, (**), ...)

> namespace Existential
>   %hide Prelude.Pairs.Exists
>   using (a : Type, P : a -> Prop)
>     data Exists : (P : a -> Prop) -> Prop where
>       Evidence : (wit : a) -> (pro : P wit) -> Exists P
      
>     getWitness : Exists {a} P -> a
>     getWitness (Evidence wit pro) = wit
      
>     getProof   : (evi : Exists {a} P) -> P (getWitness evi)
>     getProof   (Evidence wit pro) = pro

Sigma a P is basically the same as Exists {a} P
