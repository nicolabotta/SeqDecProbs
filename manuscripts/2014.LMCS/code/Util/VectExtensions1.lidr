> module VectExtensions1


> import BoundedNat.Blt
> import Logic.Postulates
> import Logic.Properties
> import Rel.Syntax


> %default total
  

> isEmpty : (n : Nat ** Vect n alpha) -> Bool
> isEmpty (_ ** Nil) = True
> isEmpty (_ ** (a :: as)) = False

> %assert_total
> isAnyBy : (alpha -> Bool) -> (n : Nat ** Vect n alpha) -> Bool
> isAnyBy _ (_ ** Nil) = False
> isAnyBy p (_ ** (a :: as)) = p a || isAnyBy p (_ ** as)

> lemma4 : (as : (n : Nat ** Vect n alpha)) ->
>          (p : alpha -> Bool) ->
>          so (isEmpty as) ->
>          so (not (isAnyBy p as))
> lemma4 (_ ** Nil) _ _ = oh
> lemma4 (_ ** (a :: as)) _ soF = soFalseElim soF

-- > lemma5 : (p  : alpha -> Bool) ->
-- >          (as : (n : Nat ** Vect n alpha)) ->
-- >          (q  : so (isAnyBy p as)) ->
-- >          (q' : so (p (head as) || isAnyBy p (tail as)))

> parameters (beta : Type,
>             eqeq : beta -> beta -> Bool,
>             --eqeqSpec1 : (b : beta) -> so (eqeq b b))
>             eqeqSpec1 : reflexive beta eqeq)

>   %assert_total
>   isIn : beta -> (n : Nat ** Vect n beta) -> Bool
>   isIn b (Z ** Nil) = False
>   isIn b ((S n) ** (b' :: bs')) = eqeq b b' || isIn b (n ** bs')

>   lemma0 : (b : beta) ->
>            (bs : Vect n beta) ->
>            so (b `isIn` (_ ** (b :: bs)))
>   lemma0 {n} b bs = step2
>   where
>     step1 : eqeq b b || (b `isIn` (n ** bs)) = True || (b `isIn` (n ** bs))
>     step1 = leibniz (\ x => b `isIn` ((S n) ** (b :: bs)) = x || (b `isIn` (n ** bs)))
>                     (soTrue (eqeqSpec1 b))
>                     refl
>     step2 : so (eqeq b b || (b `isIn` (n ** bs))) 
>     step2 = leibniz (\ x => so x) (sym step1) oh

> --    lala = leibniz (\x => so (x || b `isIn` (_ ** bs))) (sym (soTrue (eqeqSpec1 b))) oh

so (b `isIn` (b :: bs))
  
    b `isIn` (b :: bs)
=   {  refl  }
    eqeq b b || b `isIn` bs
=   {  leibniz (\x => so (x || b `isIn` bs)) (sym (soTrue (eqeqSpec1 b))) oh  }
    True
  
>   lemma1 : (b : beta) ->
>            (bs : (n : Nat ** Vect n beta)) ->
>            so (b `isIn` bs) ->
>            so (not (isEmpty bs))
>   lemma1 _ (_ ** Nil) soF = soFalseElim soF
>   lemma1 _ (_ ** (b :: bs)) _ = oh 

>   lemma2 : (bs : (n : Nat ** Vect n beta)) ->
>            so (not (isEmpty bs)) ->
>            (b : beta ** so (b `isIn` bs))
>   lemma2 (_ ** Nil) soF = soFalseElim soF
>   -- lemma2 (_ ** (b :: bs)) _ = (b ** lemma0 b (b :: bs)) ?
>   lemma2 (_ ** (b :: bs)) _ = (b ** believe_me oh)

>   lemma3 : (b : beta) ->
>            (p : beta -> Bool) ->
>            (bs : (n : Nat ** Vect n beta)) ->
>            so (p b) ->
>            so (b `isIn` bs) ->
>            so (isAnyBy p bs)
>   lemma3 _ _ (_ ** Nil) _ soF = soFalseElim soF
>   lemma3 _ _ (_ ** (b :: bs)) _ _ = believe_me oh -- ?

>   lemma6 : (p  : beta -> Bool) ->
>            (as : (n : Nat ** Vect n beta)) ->
>            so (isAnyBy p as) ->
>            (a : beta ** (so (p a), so (a `isIn` as)))
>   lemma6 p (_ ** Nil) soF = soFalseElim soF
>   lemma6 p (_ ** (a :: as)) iab = believe_me oh -- ?



Sometimes one has to do with types whose values can exhaustively be
stored in a vector. |Char| is a natural example. In these cases ist is
often useful to state (postulate, prove) that a given vector does, in
fact, contain all values of that type. We express this property by meand
of |whole|:

>   whole : (n : Nat ** Vect n beta) -> Type
>   whole bs = (b : beta) -> so (b `isIn` bs)

One intended usage of |whole| is in combination with the above |lemma3|:
if we have a value |wbs : whole bs| and we know that |b| fulfills |p|,
then we can apply |lemma3| to |b|, |p|, |bs|, |pb| *and* |wbs b| to
deduce that there is at least one element in |bs| that fulfills |p|. See
S1206_Example2 for an application.

> normalize : (m : Nat ** Vect (S m) alpha) -> (n : Nat ** Vect n alpha)
> normalize as = (S (getWitness as) ** getProof as)

> fmap : (alpha -> beta) -> 
>        (n : Nat ** Vect n alpha) -> 
>        (n : Nat ** Vect n beta)
> fmap f (_ ** Nil) = (_ ** Nil)
> fmap f (_ ** (a :: as)) = (_ ** f a :: map f as)


> fmapP : (alpha -> beta) -> 
>         (n : Nat ** Vect (S n) alpha) -> 
>         (n : Nat ** Vect (S n) beta)
> fmapP f (_ ** a :: as) = (_ ** f a :: map f as)


> fmapP' : (alpha -> beta) -> 
>          (n : Nat ** (Vect n alpha, so (n > Z))) -> 
>          (n : Nat ** (Vect n beta, so (n > Z)))
> fmapP' f (_ ** (Nil, p)) = (_ ** (Nil, p))
> fmapP' f (_ ** ((a :: as), p)) = (_ ** ((f a :: map f as), p))

> mapFilter : (alpha -> beta) ->
>             (alpha -> Bool) -> 
>             Vect n alpha -> 
>             (n : Nat ** Vect n beta)
> mapFilter f p Nil = (_ ** Nil)
> mapFilter f p (a :: as) with (p a)
>   | True  = (_  ** (f a) :: (getProof (mapFilter f p as)))
>   | False = mapFilter f p as


> filterP : (p  : alpha -> Bool) -> 
>           (as : Vect (S n) alpha) -> 
>           so (isAnyBy p (S n ** as)) ->
>           (m : Nat ** Vect (S m) alpha)
> filterP p (a :: Nil) q = (_ ** a :: Nil) 
> filterP p (a :: (a' :: as)) q = 
>   if (p a) 
>   then (_ ** (a :: getProof (filter p (a' :: as))))
>   else filterP p (a' :: as) (believe_me oh)

total filter : (a -> Bool) -> Vect a n -> (p ** Vect a p)
filter p [] = ( _ ** [] )
filter p (x::xs) with (filter p xs)
  | (_ ** tail) =
    if p x then
      (_ ** x::tail)
    else
      (_ ** tail)

> %assert_total
> filterP' : (p  : alpha -> Bool) -> 
>            (as : Vect n alpha) -> 
>            so (isAnyBy p (n ** as)) ->
>            (m : Nat ** (Vect m alpha, so (m > Z)))
> filterP' p (a :: as) q = 
>   if (p a) 
>   then (_ ** (a :: (getProof (filter p as)), oh))
>   else filterP' p as (believe_me oh)


> filterTag : (p  : alpha -> Bool) -> 
>             Vect n alpha -> 
>             (m : Nat ** Vect m (a : alpha ** so (p a)))
> filterTag _ Nil = (_ ** Nil)
> filterTag p (a :: as) with (p a)
>   | True  = (_ 
>              ** 
>              (a ** believe_me oh) :: (getProof (filterTag p as))
>             )
>   | False = filterTag p as

> filterTagP : (p  : alpha -> Bool) -> 
>              (as : Vect (S n) alpha) -> 
>              so (isAnyBy p (S n ** as)) ->
>              (m : Nat ** Vect (S m) (a : alpha ** so (p a)))
> filterTagP p (a :: Nil) q = (_ ** ((a ** believe_me (p a)) :: Nil)) 
> filterTagP p (a :: (a' :: as)) q = 
>   if (p a) 
>   then (_ ** ((a ** believe_me (p a)) 
>               :: 
>               map 
>               (\ a'' => (a'' ** believe_me (p a''))) 
>               (getProof (filter p (a' :: as)))
>              )
>        )
>   else filterTagP p (a' :: as) (believe_me oh)


> %assert_total
> filterTagP' : (p  : alpha -> Bool) -> 
>               (as : Vect n alpha) -> 
>               so (isAnyBy p (n ** as)) ->
>               (m : Nat ** (Vect m (a : alpha ** so (p a)), so (m > Z)))
> filterTagP' p (a :: as) q = 
>   if (p a) 
>   then (_ ** ((a ** believe_me (p a)) 
>               ::
>               map 
>               (\ a'' => (a'' ** believe_me (p a''))) 
>               (getProof (filter p as)), oh))
>   else filterTagP' p as (believe_me oh)


