> module Num

> import Data.Fin
> import Data.Vect
> import Data.VectType
> import Syntax.PreorderReasoning

> import Matrix
> import MatrixOperations
> import NumRefinements
> import NumOperations
> -- import FinOperations

> %default total


The following

> foldrVectLemma : {A, B : Type} -> {n : Nat} ->
>                  (f : A -> B -> B) -> (e : B) ->
>                  (a : A) -> (as : Vect n A) ->
>                  foldr f e (a :: as) = f a (foldr f e as)

should hold by definition and should be replaceable by just |Refl|. But
since |Data.VectType.foldr| is implemented in terms of an accumulator
(is there a particular reason for doing so ?) we in fact need a
(possibly non-trivial?) proof.


> total foldrClassic : (t -> acc -> acc) -> acc -> Vect n t -> acc
> foldrClassic f e [] = e
> foldrClassic f e (x::xs) = f x (foldrClassic f e xs)

> foldrImplLemma : {A, B : Type} -> {n : Nat} ->
>                  (f : A -> B -> B) -> (e : B) -> (go : B -> B) ->
>                  (as : Vect n A) ->
>                  foldrImpl f e go as = go (foldrClassic f e as)
> foldrImplLemma f e go [] = Refl
> foldrImplLemma f e go (a :: as) =
>     ( foldrImpl f e go (a :: as) )
>   ={ Refl }=
>     ( foldrImpl f e (go . (f a)) as )
>   ={ foldrImplLemma f e (go . (f a)) as }=
>     ( (go . (f a)) (foldrClassic f e as) )
>   ={ Refl }=
>     ( go (f a (foldrClassic f e as)) )
>   ={ Refl }=
>     ( go (foldrClassic f e (a :: as) ) )
>   QED

> foldrImplCorr :  {A, B : Type} -> {n : Nat} ->
>                  (f : A -> B -> B) -> (e : B) ->
>                  (as : Vect n A) ->
>                  foldrImpl f e id as = foldrClassic f e as
> foldrImplCorr f e as = foldrImplLemma f e id as

Now we can continue with the proof:

> foldrVectLemma f e a as =
>     ( foldr f e (a :: as) )
>   ={ Refl }=
>     ( foldrImpl f e id (a :: as) )
>   ={ foldrImplCorr f e (a :: as) }=
>     ( foldrClassic f e (a :: as) )
>   ={ Refl }=
>     ( f a (foldrClassic f e as) )
>   ={ cong {f = f a} (sym (foldrImplCorr f e as)) }=
>     ( f a (foldrImpl f e id as) )
>   ={ Refl }=
>     ( f a (foldr f e as) )
>   QED

> |||
> sumLemma : (Num t) => (x : t) -> (xs : Vect m t) -> sum (x :: xs) = x + sum xs
> sumLemma x xs = ( sum (x :: xs) )
>               ={ Refl }=
>                 ( foldr (+) (fromInteger 0) (x :: xs) )
>               ={ foldrVectLemma (+) (fromInteger 0) x xs }=
>                 ( x + foldr (+) (fromInteger 0) xs )
>               ={ Refl }=
>                 ( x + sum xs )
>               QED

> ||| This follows from the definition of append (because it is not defined in terms of foldr)
> appendLemma : (x : t) -> (xs : Vect m t) -> (ys : Vect n t) ->
>               ((x :: xs) ++ ys) = (x :: (xs ++ ys))
> appendLemma x xs ys =
>     ( (x :: xs) ++ ys )
>   ={ Refl }=
>     ( x :: (xs ++ ys) )
>   QED

> |||
> multSumLemma : (NumMultDistributesOverPlus t) =>
>                (x : t) -> (xs : Vect m t) ->
>                x * sum xs = sum (multSV x xs)
> multSumLemma x  Nil      = ( x * (fromInteger 0) )
>                          ={ multZeroPlusRight x }=
>                            ( fromInteger 0 )
>                          ={ Refl }=
>                            ( sum Data.VectType.Vect.Nil )
>                          QED
> multSumLemma x (y :: ys) = ( x * (sum (y :: ys)) )
>                          ={ cong (sumLemma y ys) }=
>                            ( x * (y + sum ys) )
>                          ={ NumRefinements.multDistributesOverPlusRight x y (sum ys) }=
>                            ( (x * y) + (x * sum ys) )
>                          ={ cong (multSumLemma x ys) }=
>                            ( x * y + sum (multSV x ys) )
>                          ={ sym (sumLemma (x * y) (multSV x ys)) }=
>                            ( sum (x * y :: multSV x ys) )
>                          ={ Refl }=
>                            ( sum (multSV x (y :: ys)) )
>                          QED

> sumsTo : Num t => (s : t) -> (xs : Vect m t) -> Type
> sumsTo s xs = (sum xs = s)

> sumOne : Num t => (xs : Vect m t) -> Type
> sumOne = sumsTo (fromInteger 1)

> -- lemma1 :  {t : Type} -> NumMultDistributesOverPlus t =>
> lemma1 :  (NumMultDistributesOverPlus t) =>
>           (x : t) -> (xs : Vect n t) ->
>           sumOne xs -> sumsTo x (multSV x xs)
> lemma1 x xs pxs =
>     ( sum (multSV x xs) )
>   ={ sym (multSumLemma x xs) }=
>     ( x * sum xs )
>   ={ cong pxs }=
>     ( x * fromInteger 1 )
>   ={ multOneRight x }=
>     x
>   QED

> sumPlusAppendLemma :  NumAssocPlus t =>
>                       (xs : Vect n t) -> (ys : Vect m t) ->
>                       (sum xs + sum ys) = sum (xs ++ ys)
> sumPlusAppendLemma Nil ys = plusZeroPlusLeft (sum ys)
> sumPlusAppendLemma (x :: xs) ys =
>     ( sum (x :: xs) + sum ys )
>   ={ cong {f = \a => a + sum ys} (sumLemma x xs) }=
>     ( (x + sum xs) + sum ys )
>   ={ sym (plusAssoc x (sum xs) (sum ys)) }=
>     ( x + (sum xs + sum ys) )
>   ={ cong (sumPlusAppendLemma xs ys) }=
>     ( x + sum (xs ++ ys) )
>   ={ sym (sumLemma x (xs ++ ys)) }=
>     ( sum (x :: (xs ++ ys)) )
>   ={ Refl }=
>     ( sum ((x :: xs) ++ ys) )
>   QED
>
> sumMapConcat : (NumAssocPlus t) => (xss : Matrix m n t) ->
>                sum (map sum xss) = sum (Vect.concat xss)
> sumMapConcat Nil = Refl
> sumMapConcat (row :: rows) =
>     ( sum (map sum (row :: rows)) )
>   ={ Refl }=
>     ( sum (sum row :: map sum rows) )
>   ={ sumLemma (sum row) (map sum rows) }=
>     ( sum row + sum (map sum rows) )
>   ={ cong (sumMapConcat rows) }=
>     ( sum row + sum (Vect.concat rows) )
>   ={ sumPlusAppendLemma row (Vect.concat rows) }=
>     ( sum (row ++ Vect.concat rows) )
>   ={ Refl }=
>     ( sum (Vect.concat (row :: rows)) )
>   QED


Use lemma1, sumMapConcat, etc.

Requires both NumAssocPlus and NumMultDistributesOverPlus. (And
currently there is some problem with "multiple constraints" so the
NumRefinements class may need to change to a chain instead of a tree.)

> ||| 'Tail' of a finite dependently typed function
> depTail : {n : Nat} -> {P : Fin (S n) -> Type} -> 
>           ((k : Fin (S n)) -> P k) -> ((j : Fin n) -> P (FS j))
> depTail {P} f k = f (FS k)

> |||
> multVMLemma0 : (NumAssocPlus t) => 
>                (xs : Vect m t) -> (xss : Matrix m n t) ->
>                ((k : Fin m) -> sumOne (row k xss)) -> 
>                sum (Vect.concat (multVM xs xss)) = sum xs 
> multVMLemma0 {m = Z}    {n}  Nil       Nil        _  = Refl
> multVMLemma0 {m = S m'} {n} (x :: xs) (ys :: yss) ps =
>     ( sum (Vect.concat (multVM (x :: xs) (ys :: yss))) )
>   ={ Refl }=
>     ( sum (Vect.concat ((multSV x ys) :: (multVM xs yss))) )
>   ={ sym (sumMapConcat ((multSV x ys) :: (multVM xs yss))) }=
>     ( sum (map sum ((multSV x ys) :: (multVM xs yss))) )
>   ={ Refl }=
>     ( sum (sum (multSV x ys) :: (map sum (multVM xs yss))) )
>   ={ ?lala }=
>   {-
>   ={ cong (lemma1 x ys (ps FZ)) }=
>   ={ replace {x = sum (multSV x ys)}
>              {y = x}
>              {P = \ ZUZU => sum (sum (multSV x ys) :: (map sum (multVM xs yss)))
>                             =
>                             sum (ZUZU :: (map sum (multVM xs yss)))}
>              (lemma1 x ys (ps FZ))
>              Refl }=
>   ---}
>     ( sum (x :: (map sum (multVM xs yss))) )
>   ={ sumLemma x (map sum (multVM xs yss)) }=
>     ( x + sum (map sum (multVM xs yss)) )
>   ={ cong (sumMapConcat (multVM xs yss)) }=
>     ( x + sum (Vect.concat (multVM xs yss)) )
>   ={ cong (multVMLemma0 xs yss (depTail ps)) }=
>     ( x + sum xs )
>   ={ sym (sumLemma x xs) }=           
>     ( sum (x :: xs) )
>   QED


> |||
> multVMLemma : (NumAssocPlus t) =>
>               (m : Nat) ->
>               (xs : Vect m t) -> sumOne xs ->
>               (n : Nat) ->
>               (xss : Matrix m n t) ->
>               ((k : Fin m) -> sumOne (row k xss)) ->
>               sumOne (Vect.concat (multVM xs xss))
> multVMLemma m xs pxs n xss pxss = 
>     ( sum (Vect.concat (multVM xs xss)) )
>   ={ multVMLemma0 xs xss pxss }=
>     ( sum xs )
>   ={ pxs }=
>     ( fromInteger 1 )
>   QED
>     

