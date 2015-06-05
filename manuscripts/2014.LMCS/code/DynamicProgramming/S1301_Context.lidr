> module Context

> import Data.So


> %default total


In the case of a time-dependent set of states and of a general
transition function, the context of a DP problem can be formalized in
terms of:

# A set of states |X|:

> X : Nat -> Type

# A set of controls or actions |Y t x|:

> Y : (t : Nat) -> X t -> Type

# A functor |M|

> M : Type -> Type

> Mmap : (alpha -> beta) -> M alpha -> M beta

> Mret : alpha -> M alpha

> Mbind : M alpha -> (alpha -> M beta) -> M beta

Todo: write specifications for |Mret| and |Mbind|


# A transition function:

> step : (t : Nat) -> (x : X t) -> Y t x -> M (X (S t))

# A reward function:

> reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Float

For |M = Id|, |M = List| and |M = SimpleProb| one recovers the
deterministic case, the non-deterministic case and the stochastic
case.

|step t x y| yields an |M|-structure on |X (S t)|. For the specification
of |rechable| and |viable|, see section
S1302_ReachabilityViability.lidr, one has to assess whether a given
state is contained in |M|-structure (on states):

> MisIn : alpha -> M alpha -> Bool

> MareAllTrue      :  M Bool -> Bool

> Mspec1 : (b : Bool) -> So (MareAllTrue (Mret b) == b)

> Mspec2 : (mx : M alpha) -> (p : alpha -> Bool) ->
>          So (MareAllTrue (Mmap p mx)) ->
>          (x : alpha) -> So (x `MisIn` mx) -> So (p x)


> toSub : (ma : M alpha) -> M (a : alpha ** So (a `MisIn` ma))
> toSubSpec : (ma : M alpha) -> Mmap outl (toSub ma) = ma

MmapIn : (ma : M alpha) -> (f : (a : alpha) -> So (MisIn a ma) -> beta) -> M beta

MmapInSpec : (ma : M alpha) -> (f : (a : alpha) -> So (MisIn a ma) -> beta) ->
             MmapIn ma f = Mmap (\ a => f a (believe_me oh)) ma

MbindIn : (ma : M alpha) -> (f : (a : alpha) -> So (MisIn a ma) -> M beta) -> M beta

MbindInSpec : (ma : M alpha) -> (f : (a : alpha) -> So (MisIn a ma) -> M beta) ->
             MbindIn ma f = Mbind ma (\ a => f a (believe_me oh))

Because |M| is a functor, an |M|-structure on |X (S t)| induces an
|M|-structure on rewards:

Mmap (reward t x y) (step t x y) : M Float

One can extend all the results and algorithms derived for the
deterministic case if one assumes that the controler has a measure for
evaluating such |M|-structure:

> Mmeas : M Float -> Float

and that such measure satisfies the following monotonicity condition,
see S130...

> MmeasMon  :  (f : X t -> Float) -> (g : X t -> Float) -> 
>              ((x : X t) -> So (f x <= g x)) ->
>              (mx : M (X t)) -> So (Mmeas (Mmap f mx) <= Mmeas (Mmap g mx))

> Mreward        :  (t : Nat) -> (x : X t) -> Y t x -> M Float
> Mreward t x y  =  Mmap (\ x' => reward t x y x') (step t x y)


> x0 : X 0

> y0 : Y 0 x0

> mrs  :  M Float
> mrs  =  Mmap f (step 0 x0 y0) where
>   f    :  (x : X 1) -> Float
>   f x  =  reward 0 x0 y0 x
  

> p0 : (x : X 0) -> Y 0 x

> mxy0  :  M (x : X 0 ** Y 0 x)
> mxy0  =  Mret (x0 ** p0 x0)

> mx1  :  M (X 1)
> mx1  =  step 0 x0 y0

> p1  :  (x : X 1) -> Y 1 x

> mxy1  :  M (x : X 1 ** Y 1 x)
> mxy1  =  Mmap f (step 0 x0 y0) where
>   f    :  (x : X 1) -> (x : X 1 ** Y 1 x)
>   f x  =  (x ** p1 x)

> p : (t : Nat) -> (x : X t) -> Y t x

> mxy : (t : Nat) -> M (x : X t ** Y t x)
> mxy Z = Mret (x0 ** p Z x0)
> mxy (S t) = (mxy t) `Mbind` g where  
>   g : (x : X t ** Y t x) -> M (x : X (S t) ** Y (S t) x)
>   g (xt ** yt) = Mmap f (step t xt yt) where
>     f     :  (x : X (S t)) -> (x : X (S t) ** Y (S t) x)
>     f xt  =  (xt ** p (S t) xt)

> {- 

> -}
