TODO: probably remove this module

> module SimpleProb1

> import Data.So
> import Vect.Ops
> import Util.VectExtensions1
> -- import BoundedNat.Blt


> data SimpleProb : Type -> Type where
>   SP : (aps : Vect n (alpha, Float)) ->
>        So (foldl (+) 0.0 (map snd aps) == 1.0) ->
>        SimpleProb alpha


> suppBy : (alpha -> alpha -> Bool) ->
>          SimpleProb alpha ->
>          (n : Nat ** Vect n alpha)
> suppBy {alpha} p (SP aps _) = nubBy p (getProof as) where
>  as : (n : Nat ** Vect n alpha)
>  as = mapFilter fst notz aps where
>    notz : (alpha, Float) -> Bool
>    notz (_, px) = px /= 0.0


> supp : Eq alpha =>
>        SimpleProb alpha ->
>        (n : Nat ** Vect n alpha)
> supp = suppBy (==)


> normalizeBy : (alpha -> alpha -> Bool) ->
>               SimpleProb alpha ->
>               SimpleProb alpha
> normalizeBy {alpha} p (SP aps q) = SP (getProof aps') q' where
>   f : alpha -> (alpha, Float)
>   f a = (a, foldl g 0.0 aps) where
>     g : Float -> (alpha, Float) -> Float
>     g e (b, pb) = if (p a b)
>                   then e + pb
>                   else e
>   aps' : (n : Nat ** Vect n (alpha, Float))
>   aps' = fmap f (suppBy p (SP aps q))
>   q' : So (foldl (+) 0.0 (map snd (getProof aps')) == 1.0)
>   q' = believe_me Oh


> normalize : Eq alpha => SimpleProb alpha -> SimpleProb alpha
> normalize = normalizeBy (==)


-- > eqeqBy : (alpha -> alpha -> Bool) ->
-- >          SimpleProb alpha ->
-- >          SimpleProb alpha ->
-- >          Bool
-- > eqeqBy {alpha} p sp1 sp2
-- >   =
-- >   (length ps1 == length ps2
-- >    &&
-- >    and (map (\ xp => elemBy p' xp ps2) ps1)
-- >   ) where
-- >     p' : (alpha, Float) -> (alpha, Float) -> Bool
-- >     p' (a,pa) (a',pa') = (p a a') && (pa == pa')
-- >     ps1 : List (alpha, Float)
-- >     ps1 = toList (normalizeBy p sp1)
-- >     ps2 : List (alpha, Float)
-- >     ps2 = toList (normalizeBy p sp2)

-- > eqeq : Eq alpha => SimpleProb alpha -> SimpleProb alpha -> Bool
-- > eqeq {alpha} sp1 sp2
-- >   =
-- >   (length ps1 == length ps2
-- >    &&
-- >    and (map (\ xp => xp `elem` ps2) ps1)
-- >   ) where
-- >     ps1 : List (alpha, Float)
-- >     ps1 = toList (normalize sp1)
-- >     ps2 : List (alpha, Float)
-- >     ps2 = toList (normalize sp2)

-- > return : alpha -> SimpleProb alpha
-- > return {alpha} a = SP alpha 1 [a] [1.0]

-- > bind : SimpleProb alpha ->
-- >        (alpha -> SimpleProb beta) ->
-- >        SimpleProb beta
-- > bind {alpha} {beta} sp f = SP (concat (map g (toList sp))) where
-- >   g : (alpha, Float) -> List (beta, Float)
-- >   g (a, p) = map h (toList (f a)) where
-- >     h : (beta, Float) -> (beta, Float)
-- >     h (x, p') = (x, p' * p)



-- > data X = L | A | R

-- > size : Nat
-- > size = 3

-- > probs : Vect size Float
-- > probs = [0.1, 0.4, 0.5]

-- > index : X -> Blt size
-- > index L = (0 ** Oh)
-- > index A = (1 ** Oh)
-- > index R = (2 ** Oh)

-- > xedni : Blt size -> X
-- > xedni i = case (cast (toNat i)) of
-- >   0 => L
-- >   1 => A
-- >   2 => R

-- > sp1 : SimpleProb Nat
-- > sp1 = SP X 3 probs Oh index xedni (believe_me Oh) (believe_me Oh)




-- > eqeqBy : (alpha -> alpha -> Bool) ->
-- >          SimpleProb alpha ->
-- >          SimpleProb alpha ->
-- >          Bool
-- > eqeqBy {alpha} p sp1 sp2
-- >   =
-- >   (length ps1 == length ps2
-- >    &&
-- >    and (map (\ xp => elemBy p' xp ps2) ps1)
-- >   ) where
-- >     p' : (alpha, Float) -> (alpha, Float) -> Bool
-- >     p' (a,pa) (a',pa') = (p a a') && (pa == pa')
-- >     ps1 : List (alpha, Float)
-- >     ps1 = toList (normalizeBy p sp1)
-- >     ps2 : List (alpha, Float)
-- >     ps2 = toList (normalizeBy p sp2)

-- > eqeq : Eq alpha => SimpleProb alpha -> SimpleProb alpha -> Bool
-- > eqeq {alpha} sp1 sp2
-- >   =
-- >   (length ps1 == length ps2
-- >    &&
-- >    and (map (\ xp => xp `elem` ps2) ps1)
-- >   ) where
-- >     ps1 : List (alpha, Float)
-- >     ps1 = toList (normalize sp1)
-- >     ps2 : List (alpha, Float)
-- >     ps2 = toList (normalize sp2)

-- return (Nicola 22.01.2013)

-- > return : alpha -> SimpleProb alpha
-- > return a = SP [(a, 1.0)]

-- bind (Nicola 22.01.2013)

-- > bind : SimpleProb alpha ->
-- >        (alpha -> SimpleProb beta) ->
-- >        SimpleProb beta
-- > bind {alpha} {beta} sp f = SP (concat (map g (toList sp))) where
-- >   g : (alpha, Float) -> List (beta, Float)
-- >   g (a, p) = map h (toList (f a)) where
-- >     h : (beta, Float) -> (beta, Float)
-- >     h (x, p') = (x, p' * p)

-- We can now define |SimpleProb| as an instance of the typeclasses |Eq|
-- and |Monad|.

-- -- > instance Eq a => Eq (SimpleProb a) where
-- -- >   sp1 == sp2 = length ps1 == length ps2 &&
-- -- >                and (map (`elem` ps2) ps1)
-- -- >                where
-- -- >                ps1 = toList (normalizeSP sp1)
-- -- >                ps2 = toList (normalizeSP sp2)

-- > instance Eq alpha => Eq (SimpleProb alpha) where
-- >   (==) = eqeq

-- -- > instance Monad SimpleProb where
-- -- >   return a = SP [(a, 1.0)]
-- -- >   SP (ds1) >>= f = SP (concat (map g ds1))
-- -- >                    where
-- -- >                    g (a, p) = map h (toList (f a))
-- -- >                               where
-- -- >                               h (x, p') = (x, p'*p)

-- > instance Functor SimpleProb where
-- >   fmap f sp = bind sp (return . f)

-- > instance Applicative SimpleProb where
-- >   pure = return
-- >   sp1 <$> sp2 = bind sp1 (\f => bind sp2 (return . f))

-- > instance Monad SimpleProb where
-- >   return = SimpleProb.return
-- >   (>>=) = bind

-- The monadic bind operator expresses the conditional probabilities of
-- the elements in the target of |f|, depending on the distribution on
-- the elements in the source of |f|.  For finite, identical source and
-- target, |f| can be represented as a stochastic matrix, and the bind
-- operator gives the transition of the associated markov chain.

-- Nicola 22.01.2013: we start to implement here functionalities for
-- working with |SimpleProbs|s:

-- Construction

-- -- > concentrated : a -> SimpleProb a
-- -- > concentrated = return

-- -- > uniform : [a] -> SimpleProb a
-- -- > uniform xs = SP [(x, p) | x <- xs] where
-- -- >   p = 1.0 / (realToFrac (length xs))

-- > convComb : Float ->
-- >            SimpleProb alpha ->
-- >            SimpleProb alpha ->
-- >            SimpleProb alpha
-- > convComb {alpha} t sp1 sp2 = SP (aps1 ++ aps2) where
-- >   aps1 : List (alpha, Float)
-- >   aps1 = rescale t (toList sp1)
-- >   aps2 : List (alpha, Float)
-- >   aps2 = rescale (1.0 - t) (toList sp2)


-- Evaluation:

-- > eval : Eq a => SimpleProb a -> a -> Float
-- > -- eval (SP xps) x = sum ([p | (x', p) <- xps, x' == x])
-- > eval (SP xps) x = foldl (+) 0 ([p | (x', p) <- xps, x' == x])

-- Expected value:

-- > eValue : SimpleProb Float -> Float
-- > eValue (SP xps) = foldl f 0 xps where
-- >   f : Float -> (Float, Float) -> Float
-- >   f e (x,p) = e + x * p
