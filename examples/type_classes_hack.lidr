> class Preorder t where
>   total C : t -> t -> Type
>   total reflexive : (x : t) -> C x x
>   total transitive : (x : t) -> (y : t) -> (z : t) -> 
>                      C x y -> C y z -> C x z

> class (Preorder t) => TotalPreorder t where
>   total either : (x : t) -> (y : t) -> Either (C x y) (C y x)


> instance [fstPreorder] Preorder a => Preorder (a, b) where
>   C x y = C (fst x) (fst y)
>   reflexive x = reflexive (fst x)
>   transitive x y z xy yz = transitive (fst x) (fst y) (fst z) xy yz

> instance [sndPreorder] Preorder b => Preorder (a, b) where
>   C x y = C (snd x) (snd y)
>   reflexive x = reflexive (snd x)
>   transitive x y z xy yz = transitive (snd x) (snd y) (snd z) xy yz

Now, let's "solve" the problem, for values of "solve" that include
"work around in an ugly manner". Given a Preorder dictionary, what do
we need to know to construct a TotalPreorder? The answer is that we
need an implementation of Either, using the correct C relations
projected from the dictionary:

> hackTy : (dict : Preorder a) -> Type
> hackTy dict = (x : a) -> (y : a) -> Either (C @{dict} x y) (C @{dict} y x)

We have the dictionary as the argument in order to make the Cs be the
right Cs, and get the necessary equalities.

Now, because constraints aren't a separate kind in Idris as they are
in Haskell, we can put non-constraint things in a constraint position
on a named instance to achieve a means of passing it an arbitrary
argument (in this case, an "either" implementation). Basically, this
thing expands to a function that directly calls the constructor of the
underlying hidden record type.

> instance [horribleHack] (dict : Preorder a, fun : hackTy dict) => TotalPreorder a where
>   either @{preorder} @{fun} x y = fun x y

Now that we can construct dictionaries ourselves, we can do what Idris
expands the named instance declaration to. For "fstTotalPreorder", we
first use type class resolution for "Preorder a" together with our
named instance "fstPreorder" to get a preorder on (a, b). Then,
"fstEither" delegates to the "TotalPreorder a" instance. Finally,
"horribleHack" is used to tie it all together into a real instance.

> fstTotalPreorder : TotalPreorder a => TotalPreorder (a, b)
> fstTotalPreorder @{totdict} = let dict : Preorder (a, b) = fstPreorder
>                                   fstEither = \x,y => either @{totdict} (fst x) (fst y)
>                               in horribleHack @{dict} @{fstEither}

The same trick works for "sndTotalPreorder":

> sndTotalPreorder : TotalPreorder b => TotalPreorder (a, b)
> sndTotalPreorder @{totdict} = horribleHack @{dict} @{sndEither} where
>   dict : Preorder (a, b) 
>   dict = sndPreorder
>   sndEither : hackTy dict
>   sndEither = \x,y => either @{totdict} (snd x) (snd y)



This gets you what you want, but it's hardly an example of good Idris style...

/David



