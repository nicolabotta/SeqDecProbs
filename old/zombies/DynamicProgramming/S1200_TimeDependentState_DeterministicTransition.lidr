> module Main

> import Float.Properties
> import BoundedNat.Blt
> import Util.VectExtensions1
> import Util.Util
> import Util.Opt
> import Exists.Ops

> %default total

So far, we have assumed the set of states |X| to be constant. But, in most
practical cases, the set of states a system can take after, say, |k|
iterations will, in general, depend on |k|.

Consider, for istance, the problem of S1106__Example1. There the state is
defined as

< X = Blt nColumns

and, according to the definition of |Blt n| given in
BoundedNat/Blt.lidr, |x : X| is a natural number smaller than
|nColumns|. It is useful to think of this number as that of a column
index.

The controls are admissible actions (|{A,R}|, |{L,A,R}| or |{L,A}|
depending on the state i.e. column index) and a sequence of admissible
controls of length |n| for an initial state |x0| defines, through
|step|, a unique sequence of states.

For instance, the sequence of controls [R,R,R,R,A,A] is feasible for |x0
= 0| and defines the sequence of column indexes [0,1,2,3,4,4,4], see
Fig. 1.

    6   | | | | |*|
    5   | | | | |*|
    4   | | | | |*|
    3   | | | |*| |
    2   | | |*| | |
    1   | |*| | | |
    0   |*| | | | |

         0 1 2 3 4

Fig. 1 Constant state, deterministic transition

This sequence is represented in Fig. 1 by the symbol |*|. We read the
table sketched in Fig. 1 as:

    x0 = 0, 
    x1 = 1,
    ...
    x6 = 4.

The table consists of 7 rows. The 0-th row (bottom row in Fig. 1)
represents the set of possible initial states. The 1-st row represents
the set of states after one iteration and so on. The 6-th row (top)
represents the states after 6 iterations. At each row, the column index
can be any of 0, 1, 2, 3 or 4. Thus, the table has 5 columns as stated
above.

We want now to model a situation in which the set of states the system
can take after |k| iterations does depend on |k|. For instance, we want
to model a situation in which |nColumns| depends on the number of
iterations as in Fig. 2 left or, equivalently, a situation in which
|nColumns| is constant but certain colunm indexes are not "valid",
Fig. 2, right:

    6   | | | | | |            6   | | | | | |
    5   | | |                  5   | |x| | |x|
    4   | | | | |              4   | |x| |x| |
    3   | | | |                3   |x|x|x| | |
    2   | | | | | |            2   | | | | | |
    1   | | | | | |            1   | |x| | | |
    0   | | | | |              0   | |x| | | |

         0 1 2 3 4                  0 1 2 3 4

Fig. 2: Time dependent state, crossed entries represent non-valid states

For instance, given |nColumns : Nat -> Nat|, one could model the system
sketched in Fig. 2 left with
  
<  X : Nat -> Type
<  X t = Blt (nColumns t)

or

<  X : Type
<  X = (t : Nat ** Blt (nColumns t))

Similarly, given |nColumns : Nat|, the system on the right in Fig. 2
could be modeled as

<  X : Nat -> Type
<  X t = Blt nColumns -> Bool

where |X t x == True| posits that, at time |t|, the column index |x|
is valid. The formulation

> X : Nat -> Type

has turned out to be slightly more convenient, e.g., for the
specification of |step|. With such formulation, the set of feasible
(admissible) controls becomes itself time dependent:

> Y : (t : Nat) -> X t -> Type

And |step|, |reward| can be naturally extended to:

> step : (t : Nat) -> (x : X t) -> Y t x -> X (S t)

> reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Float

As usual when dealing with dynamical systems, we say that "the system"
implicitly defined by |step| is autonomous if |step| does not explicitly
depend on time i.e.:

< step t x y = step' x y where

|step'| does not use |t| anywhere.

One could think that the natural extensions of |Policy|, |PolicySeq|,
|Val|, |max| etc. is:

> Policy : Nat -> Type
> Policy t = (x : X t) -> Y t x

> data PolicySeq : Nat -> Nat -> Type where
>   Nil : PolicySeq t Z
>   (::) : Policy t -> PolicySeq (S t) n -> PolicySeq t (S n)

> Val : (t : Nat) ->
>       (n : Nat) ->
>       (x : X t) -> 
>       PolicySeq t n -> 
>       Float
> Val _ Z _ _ = 0
> Val t (S n) x (p :: ps) = reward t x y x' + Val (S t) n x' ps where
>   y : Y t x
>   y = p x
>   x' : X (S t) 
>   x' = step t x y

> OptPolicySeq : (t : Nat) -> (n : Nat) -> PolicySeq t n -> Type
> OptPolicySeq t n ps = (ps' : PolicySeq t n) -> 
>                       (x : X t) ->
>                       so (Val t n x ps' <= Val t n x ps)

> nilIsOptPolicySeq : OptPolicySeq t Z Nil
> nilIsOptPolicySeq _ _ = reflexive_Float_lte 0

> max : (x : X t) -> 
>       (f : Y t x -> Float) -> 
>       Float

> argmax : (x : X t) -> 
>          (f : Y t x -> Float) -> 
>          Y t x

> maxSpec : (x : X t) ->
>           (f : Y t x -> Float) -> 
>           (y : Y t x) -> 
>           so (f y <= Main.max x f)

> argmaxSpec : (x : X t) ->
>              (f : Y t x -> Float) -> 
>              so (f (argmax x f) == Main.max x f)

> optExtension : (t : Nat) -> 
>                (n : Nat) -> 
>                PolicySeq (S t) n -> 
>                Policy t
> optExtension t n ps = p where
>   p : Policy t
>   p x = yq where 
>     yq : Y t x
>     yq = argmax x f where
>       f : Y t x -> Float  
>       f y = reward t x y x' + Val (S t) n x' ps where
>         x' : X (S t)
>         x' = step t x y

> backwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n
> backwardsInduction _ Z = Nil
> backwardsInduction t (S n) = ((optExtension t n ps) :: ps) where
>   ps : PolicySeq (S t) n
>   ps = backwardsInduction (S t) n

As it turns out, however, this approach is too simplistic. Consider
the case that, for |t < 3| and |t > 3| all column indexes in |Blt 5| are
valid. For |t = 3|, however, only column 4 is valid, see Fig. 3 below.

    6   | | | | | |
    5   | | | | | |
    4   | | | | | |
    3   |x|x|x|x| |
    2   | | | | | |
    1   | | | | | |
    0   | | | | | |

         0 1 2 3 4

Fig. 3: Time dependent state, crossed entries represent non-valid states

Following the Ansatz outlined above, we would model this as follows:

> nColumns : Nat
> nColumns = 5

> valid : Nat -> Blt nColumns -> Bool
> valid t i = t /= 3 || outl i > 3

> X t = (i : Blt nColumns ** so (valid t i))

> column : X t -> Nat
> column x = outl (outl x)

> (==) : X t -> X t -> Bool
> (==) x x' = column x == column x'

> states : (t : Nat) -> (n : Nat ** Vect n (X t))
> states t = zs where
>   xs : Vect nColumns (Blt nColumns)
>   xs = toVect (\ i => i)
>   ys : (n : Nat ** Vect n (Blt nColumns))
>   ys = filter (valid t) xs
>   zs : (n : Nat ** Vect n (X t))
>   zs = (_ ** map f (outr ys)) where
>     f : Blt nColumns -> X t
>     f i = (i ** believe_me (valid t i))  

> data Action = Left | Ahead | Right

> instance Show Action where
>   show Left = "L"
>   show Ahead = "A"
>   show Right = "R"

> %assert_total
> admissible : X t -> Action -> Bool
> admissible {t} x Ahead = 
>   valid (S t) (outl x)
> {-
> admissible {t} x Left  = 
>   column x /= Z 
>   && 
>   valid (S t) (decBlt (outl x) (let res : (Blt.toNat (outl x) = S m) = (believe_me refl) in res))
> -}
> admissible {t} x Left = f (outl x) where
>   f : Blt nColumns -> Bool
>   f (Z ** p)   = False
>   f (S m ** p) = valid (S t) (m ** Sid_preserves_LT p)
> admissible {t} x Right = 
>   S (column x) /= nColumns
>   &&
>   valid (S t) (incBlt (outl x) (believe_me oh))

> Y t x = (a : Action ** so (admissible x a))

-- > admissiblesP : (x : X t) -> (n : Nat ** Vect (S n) (Y t x))
-- > admissiblesP {t} x = step2 where
-- >   step1 : (k : Nat ** Vect (S k) Action)
-- >   step1 = filterP (admissible x) [Left, Ahead, Right] (believe_me oh) -- !
-- >   step2 : (k : Nat ** Vect (S k) (Y t x))
-- >   step2 = fmapP g step1 where
-- >     g : Action -> Y t x
-- >     g a = (a ** believe_me (admissible x a))  

> step' : Nat -> Action -> Nat
> step' (S i) Left  = i
> step' i     Ahead = i
> step' i     Right = S i
> step' Z     Left  = Z -- should never be reached

> step'Lemma : (x : X t) -> 
>              (a : Action) ->
>              so (admissible x a) ->
>              so (step' (column x) a < nColumns)
> step'Lemma x a q = believe_me True

> step t x y = ((i' ** p') ** (believe_me oh)) 
>   where
>   a : Action
>   a = outl y
>   i' : Nat
>   i' = step' (column x) a
>   p : so (admissible x a)
>   p = outr y
>   p' : so (i' < nColumns)
>   p' = step'Lemma x a p

> reward t x y x' =
>                if column {t = S t} x' == Z
>                   then 2.0
>                   else if S (column {t = S t} x') == nColumns
>                        then 1.0
>                        else 0.0

-- > yfysP : (x : X t) -> 
-- >         (f : Y t x -> Float) -> 
-- >         (k : Nat ** Vect (S k) (Y t x, Float))
-- > yfysP {t} x f = fmapP (pair (id,f)) (admissiblesP x)

> -- max x f = snd (maxP (outr (yfysP x f)))
> max {t = t} x f = snd (maxP {n = k} yfys) where
>   as : Vect 3 Action
>   as = [Left, Ahead, Right]
>   aas : (n : Nat ** Vect (S n) Action)
>   aas = h (outr (filter (admissible x) as)) where
>      %assert_total
>      h : Vect p a -> (p : Nat ** Vect (S p) a)
>      h {p = S q} v = (q ** v)
>   ys : (n : Nat ** Vect (S n) (Y t x))
>   ys = fmapP (\ a => (a ** believe_me (admissible x a))) aas
>   kyfys : (n : Nat ** Vect (S n) (Y t x, Float))
>   kyfys = fmapP (pair (id,f)) ys
>   k : Nat
>   k = outl kyfys
>   yfys : Vect (S k) (Y t x, Float)
>   yfys = outr kyfys

> -- argmax x f = fst (maxP (outr (yfysP x f)))
> argmax {t = t} x f = fst (maxP {n = k} yfys) where
>   as : Vect 3 Action
>   as = [Left, Ahead, Right]
>   aas : (n : Nat ** Vect (S n) Action)
>   aas = h (outr (filter (admissible x) as)) where
>      %assert_total  
>      h : Vect p a -> (p : Nat ** Vect (S p) a)
>      h {p = S q} v = (q ** v)
>   ys : (n : Nat ** Vect (S n) (Y t x))
>   ys = fmapP (\ a => (a ** believe_me (admissible x a))) aas
>   kyfys : (n : Nat ** Vect (S n) (Y t x, Float))
>   kyfys = fmapP (pair (id,f)) ys
>   k : Nat
>   k = outl kyfys
>   yfys : Vect (S k) (Y t x, Float)
>   yfys = outr kyfys

> maxSpec x f y = believe_me oh -- ?

> argmaxSpec x f = believe_me oh -- ?

The computation of an optimal sequence of actions could then easily be
implemented as:

> nSteps : Nat
> nSteps = 4

> ps : PolicySeq Z nSteps
> ps = backwardsInduction Z nSteps

> controls : (t : Nat) -> 
>            (n : Nat) -> 
>            (x : X t) -> 
>            PolicySeq t n -> 
>            Vect n Action
> controls _ Z _ _ = Nil
> controls t (S n) x (p :: ps) =
>   ((outl y) :: (controls (S t) n x' ps)) where
>     y : Y t x    
>     y = p x
>     x' : X (S t)
>     x' = step t x y

> x0 : X Z
> x0 = ((1 ** oh) ** oh)

> as : Vect nSteps Action
> as = controls Z nSteps x0 ps

> main : IO ()
> main = putStrLn (show as)

There are a number of problems with this approach. The most obvious one
is that there is no sequence of admissible actions of length >= 3 when
starting in column 0. From there, one could make two steps to the right
as sketched in Figure 4:


    6   | | | | | |
    5   | | | | | |
    4   | | | | | |
    3   |x|x|x|x| |
    2   | | |*| | |
    1   | |*| | | |
    0   |*| | | | |

         0 1 2 3 4

Fig. 4: When starting from column zero, there is no sequence of
admissible controls of length >= 3.

After two steps, however, one would be stuck at column 2 with no
admissible controls to proceed. This shows that column 0 is -- as far as
the capability of making at least 3 steps is concerned -- different from
the other columns. 

We say that, at time 0, column 0 is viable for at most two steps. All
other columns are viable (again, at time zero) for an arbitrary number
of steps. We formalize the notion of viability in the next section.

Another problem of the approach outlined above is that it yields wrong
results. One has, for |nSteps = 4| and starting in column 1:

  show as
  "[L, A, L, A]" : String

This sequence of controls leads through column -1 at time 2 which is
non-valid. It is easy to understand what goes wrong by looking at the
implementation of |admissiblesP|. 

|admissiblesP| is supposed to take an |x : X t| and compute a non-empty
vector of controls that is, actions which are admissible for that
|x|. Zbviously, such function cannot be implemented: as we have seen,
there are no admissible controls in column zero at time 2. This can be
easily verified by inspection. Set

> x20 : X 2
> x20 = ((0 ** oh) ** oh)

and, from the command line, compute

  Prelude.Vect.filter (admissible x20) [Left, Ahead, Right] 
  (Z ** Prelude.Vect.Nil) : (p ** Vect Action p) 

Now |admissiblesP| is implemented in terms of |filterP|. This function,
defined in |Util/VectExtensions1.lidr|, takes a predicate on a type, a
non-empty vector of elements of that type, |as|, and a proof that |as|
contains at least one element that satisfies that predicate. It computes
a non-empty vector of those elements of |as| that satisfy that
predicate. 

The error is how |filterP| is used in |admissiblesP|: while we do not
(and, as we saw, can not) have a proof that for all |x : X| at least one
of |[Left, Ahead, Right]| is admissible in that |x|, we pretend, via
suspension of disbelief, to have one such proofs in the computation of
|step1|. This yields, from the command line again:

  filterP (admissible x20) [Left, Ahead, Right] (believe_me oh)
  (O ** Prelude.Vect.:: Main.Right (Prelude.Vect.Nil)) : (m ** Vect Action (S m))

and, ultimately, the erroneous sequence of controls reported above. In
the next section, we show how to avoid such pitfalls. As anticipated,
the idea is to recognize that, in computing optimal sequences of
controls of length |S n| (from a state which is viable for |S n| steps),
only those controls should be considered that lead to states which are
viable for |n| steps. The definition of |S n| viability has to be 
strong enough to ensure that such controls do exist.

Another notion that we will introduce in the next section is that of 
reachability. The fact that columns 0 to 3 are not valid at time 3 
implies that, in our example, the states marked with 'v' in Figure 5 are 
not viable for more than 2 steps.



    6   |r| | | | |
    5   |r|r| | | |
    4   |r|r|r| | |
    3   |x|x|x|x| |
    2   |v|v|v| | |
    1   |v|v| | | |
    0   |v| | | | |

         0 1 2 3 4
        
Fig. 5: non-viable (v) and non-reachable states. 

Similarly, the states marked with 'r' at time 4, 5 and 6 cannot be 
reached from any initial state in 4, 5 and 6 steps respectively.

While the computation of optimal policies under viability and
reachability constraints requires some additional computations, it also
can result in computational benefits.

So far, we have not attempted to account for and take (computational)
advantage of situations which may arise because of the particular form
of |Y t|. Consider the case |X t = Blt 5| and the admissible controls
are

  - {A}   for x == 0
  - {L}   for x == 1
  - {L,R} for x == 2
  - {R}   for x == 3
  - {A}   for x == 4

independently of time. In this case the entries marked with |r| in
Fig. 6 are unreachable. That is, there is no initial state and sequence
of feasible controls leading into such states.

    6   | |r|r|r| |
    5   | |r|r|r| |
    4   | |r|r|r| |
    3   | |r|r|r| |
    2   | |r|r|r| |
    1   | | |r| | |
    0   | | | | | |

         0 1 2 3 4

Fig. 6: unreachable states.

In computing optimal sequnces of policies, one can try to take advantage
of this fact and, e.g., in |optExtension|, restrict the computation of
|argmax x| only to those states which are reachable.

In the next section, we formalize the notions of reachability and
viability for the case in which the set of states |X| is time
dependent. Reachability and viability for constant states follow as a
special case.

