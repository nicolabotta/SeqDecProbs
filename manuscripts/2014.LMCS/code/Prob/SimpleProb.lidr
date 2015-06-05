> module SimpleProb


> import List.Ops


A simple probability distribution is one with a finite (or at most
countable) support, so what we want is something like the following:

< type Supp a = [a]

to represent the support, and 

< Prob : Type
< Prob = Float

< newtype SimpleProb a = SP (a -> Prob, Supp a)

to represent the distribution.  Unfortunately, we can not declare
this new type to be an instance of the monad class, since we can
only define the |return| and |(>>=)| operations on types which are
instances of |Eq|.  (For a similar reason, the Haskell implementation
of the powerset functor, |Set|, cannot be declared to be an instance
of the |Monad| type class.)

Therefore, we shall adopt the representation used by Erwig in
\cite{Erwig:pfp}:

> data SimpleProb a = SP (List (a, Float)) -- deriving Show

> toList         : SimpleProb a -> List (a, Float)
> toList (SP ds) = ds

The support of a simple probability distribution |ds| is the set of
values in the list |map fst ds|, but now we need to ensure that there
are no values associated to zero probability:

> suppBy : (alpha -> alpha -> Bool) -> 
>          SimpleProb alpha -> 
>          List alpha
> suppBy p (SP ds) = nubBy p (map fst (filter notz ds)) where 
>  notz : (alpha, Float) -> Bool
>  notz (x, px) = px /= 0

> supp : Eq a => SimpleProb a -> List a
> supp = suppBy (==)

The main difference between the list-based representation and the
functional one is that we can now have several values associated
with the same element, and values associated to zero probability
(which are therefore outside the support).  This makes it necessary
to introduce a function that normalizes the representation:

-- > normalizeSP : Eq a => SimpleProb a -> SimpleProb a
-- > normalizeSP (SP ds) = SP (map (pair (id, f)) (supp (SP ds))) where
-- >   f : a -> Float
-- >   f a = sum [p | (x, p) <- ds, x == a]

> normalizeBy : (alpha -> alpha -> Bool) -> 
>               SimpleProb alpha -> 
>               SimpleProb alpha
> normalizeBy {alpha} p (SP ds) = SP (map f (suppBy p (SP ds))) where
>   f : alpha -> (alpha, Float)
>   f a = (a, sum (map snd (filter (\ xpx => p (fst xpx) a) ds)))

> normalize : Eq alpha => SimpleProb alpha -> SimpleProb alpha
> normalize = normalizeBy (==)

== (Nicola 22.01.2013)

> eqeqBy : (alpha -> alpha -> Bool) -> 
>          SimpleProb alpha -> 
>          SimpleProb alpha -> 
>          Bool
> eqeqBy {alpha} p sp1 sp2
>   =
>   (length ps1 == length ps2 
>    && 
>    and (map (\ xp => elemBy p' xp ps2) ps1)
>   ) where 
>     p' : (alpha, Float) -> (alpha, Float) -> Bool
>     p' (a,pa) (a',pa') = (p a a') && (pa == pa')
>     ps1 : List (alpha, Float)
>     ps1 = toList (normalizeBy p sp1)
>     ps2 : List (alpha, Float)
>     ps2 = toList (normalizeBy p sp2)  

> eqeq : Eq alpha => SimpleProb alpha -> SimpleProb alpha -> Bool
> eqeq {alpha} sp1 sp2
>   =
>   (length ps1 == length ps2 
>    && 
>    and (map (\ xp => xp `elem` ps2) ps1)
>   ) where 
>     ps1 : List (alpha, Float)
>     ps1 = toList (normalize sp1)
>     ps2 : List (alpha, Float)
>     ps2 = toList (normalize sp2)  
  
return (Nicola 22.01.2013)

> return : alpha -> SimpleProb alpha
> return a = SP [(a, 1.0)]

bind (Nicola 22.01.2013)

> bind : SimpleProb alpha -> 
>        (alpha -> SimpleProb beta) -> 
>        SimpleProb beta
> bind {alpha} {beta} sp f = SP (concat (map g (toList sp))) where
>   g : (alpha, Float) -> List (beta, Float)
>   g (a, p) = map h (toList (f a)) where
>     h : (beta, Float) -> (beta, Float)
>     h (x, p') = (x, p' * p)

We can now define |SimpleProb| as an instance of the typeclasses |Eq|
and |Monad|.

-- > instance Eq a => Eq (SimpleProb a) where
-- >   sp1 == sp2 = length ps1 == length ps2 &&
-- >                and (map (`elem` ps2) ps1)
-- >                where 
-- >                ps1 = toList (normalizeSP sp1)
-- >                ps2 = toList (normalizeSP sp2)

> instance Eq alpha => Eq (SimpleProb alpha) where
>   (==) = eqeq

-- > instance Monad SimpleProb where
-- >   return a = SP [(a, 1.0)]
-- >   SP (ds1) >>= f = SP (concat (map g ds1))
-- >                    where
-- >                    g (a, p) = map h (toList (f a))
-- >                               where
-- >                               h (x, p') = (x, p'*p)

> instance Functor SimpleProb where
>   map f sp = bind sp (SimpleProb.return . f)

> instance Applicative SimpleProb where
>   pure = SimpleProb.return
>   sp1 <*> sp2 = bind sp1 (\f => bind sp2 (SimpleProb.return . f))

> instance Monad SimpleProb where
>   -- return = SimpleProb.return
>   (>>=) = bind

The monadic bind operator expresses the conditional probabilities of
the elements in the target of |f|, depending on the distribution on
the elements in the source of |f|.  For finite, identical source and
target, |f| can be represented as a stochastic matrix, and the bind
operator gives the transition of the associated markov chain.

Nicola 22.01.2013: we start to implement here functionalities for
working with |SimpleProbs|s:

Construction

-- > concentrated : a -> SimpleProb a
-- > concentrated = return

-- > uniform : [a] -> SimpleProb a
-- > uniform xs = SP [(x, p) | x <- xs] where 
-- >   p = 1.0 / (realToFrac (length xs))

> convComb : Float -> 
>            SimpleProb alpha -> 
>            SimpleProb alpha -> 
>            SimpleProb alpha
> convComb {alpha} t sp1 sp2 = SP (aps1 ++ aps2) where
>   aps1 : List (alpha, Float)
>   aps1 = rescale t (toList sp1)
>   aps2 : List (alpha, Float)
>   aps2 = rescale (1.0 - t) (toList sp2)


Evaluation:

> eval : Eq a => SimpleProb a -> a -> Float
> -- eval (SP xps) x = sum ([p | (x', p) <- xps, x' == x])
> eval (SP xps) x = foldl (+) 0 ([p | (x', p) <- xps, x' == x])

Expected value:

> eValue : SimpleProb Float -> Float
> eValue (SP xps) = foldl f 0 xps where
>   f : Float -> (Float, Float) -> Float
>   f e (x,p) = e + x * p

