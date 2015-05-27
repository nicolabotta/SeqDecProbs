> module main

> import Logic.Properties
> -- import Logic.Ops
> import Fun.Ops
> import Rel.DecEq
> import Rel.ReflDecEq
> import Float.Postulates
> import Float.Properties
> import BoundedNat.Blt
> import Util.Opt

> %default total
  

# The context (example specific):

> nColumns : Nat
> nColumns = 5

> X : Type
> X = Blt nColumns

> column : X -> Nat
> column = getWitness

> data Pos = Left | Right | Middle 

> instance Eq Pos where
>   (==) Left Left = True
>   (==) Left _ = False
>   (==) Right Right = True
>   (==) Right _ = False
>   (==) Middle Middle = True
>   (==) Middle _ = False

> pos : (x : X) -> Pos
> pos x = if column x == 0
>         then Left
>         else if (S (column x)) == nColumns
>              then Right
>              else Middle

> data Action = L | A | R

> instance Show Action where
>   show L = "L"
>   show A = "A"
>   show R = "R"
           
> data AreAdmissible : Action -> Pos -> Type where
>   lm : AreAdmissible L Middle
>   lr : AreAdmissible L Right
>   al : AreAdmissible A Left
>   am : AreAdmissible A Middle
>   ar : AreAdmissible A Right
>   rl : AreAdmissible R Left
>   rm : AreAdmissible R Middle

> Y : X -> Type
> Y x = (a : Action ** AreAdmissible a (pos x))

> max' : (x : X) -> (Y x -> Float) -> (Y x , Float)
> max' x f = maxHelp (pos x) f 
>   where
>   maxHelp               : (p : Pos) -> 
>                           ((a : Action ** AreAdmissible a p) -> Float) ->
>                           ((a : Action ** AreAdmissible a p), Float)
>   maxHelp  Left    f    =    max2' ((A ** al), (f (A ** al))) 
>                                    ((R ** rl), (f (R ** rl)))
>   maxHelp  Right   f    =    max2' ((L ** lr), (f (L ** lr))) 
>                                    ((A ** ar), (f (A ** ar)))
>   maxHelp  Middle  f    =    max3' ((L ** lm), (f (L ** lm))) 
>                                    ((A ** am), (f (A ** am))) 
>                                    ((R ** rm), (f (R ** rm)))

> max : (x : X) -> (Y x -> Float) -> Float
> max x f = snd (max' x f)

> argmax : (x : X) -> (Y x -> Float) -> Y x
> argmax x f = fst (max' x f)

> MaxSpec : Type
> MaxSpec = (x : X) ->
>           (f : Y x -> Float) ->
>           (y : Y x) ->
>           so (f y <= max x f)

> maxSpec : MaxSpec
> maxSpec x f y = believe_me oh

> ArgmaxSpec : Type
> ArgmaxSpec = (x : X) ->
>              (f : Y x -> Float) ->
>              so (f (argmax x f) == max x f)

> argmaxSpec : ArgmaxSpec
> argmaxSpec x f = believe_me oh

> step' : Nat -> Action -> Nat
> step' (S i) L = i
> step' i     A = i
> step' i     R = S i
> -- dummy case, should never be called
> step' Z     L = Z

> step'Lemma : (x : X) -> 
>              (a : Action) ->
>              AreAdmissible a (pos x) ->
>              so (step' (column x) a < nColumns)
> step'Lemma x a asm = believe_me oh

> step : (x : X) -> Y x -> X
> step x y = (x' ** p') where
>   a : Action
>   a = getWitness y
>   x' : Nat
>   x' = step' (column x) a
>   apxAreAdmissible : AreAdmissible a (pos x)
>   apxAreAdmissible = getProof y
>   p' : so (x' < nColumns)
>   p' = step'Lemma x a apxAreAdmissible

> reward : (x : X) -> Y x -> X -> Float
> reward x y x' = if column x' == Z
>                 then 1.0
>                 else if S (column x') == nColumns
>                   then 2.0
>                   else 0.0


# Generic DP:

# S1102

Sequences of feasible controls can be represented by values of type

-- > CtrlSeq : X -> Nat -> Type
-- > CtrlSeq _ Z = ()
-- > CtrlSeq x (S n) = (y : Y x ** CtrlSeq (step x y) n)

> data CtrlSeq : X -> Nat -> Type where
>   Nil : CtrlSeq x Z
>   (::) : (y : Y x) -> CtrlSeq (step x y) n -> CtrlSeq x (S n)

The sum of the rewards obtained in n steps when starting in x is

-- > val : (x : X) -> (n : Nat) -> CtrlSeq x n -> Float
-- > val _ Z _ = 0
-- > val x (S n) (y ** ys) = reward x y x' + val x' n ys where
-- >   x' : X  
-- >   x' = step x y

> val : CtrlSeq x n -> Float
> -- val Nil = 0
> -- val {x} (y :: ys) = reward x y (step x y) + val ys
> val {x} {n = Z} _ = 0
> val {x} {n = S m} (y :: ys) = reward x y (step x y) + val ys

A sequence of n feasible controls is optimal when starting in x if no
other sequence of feasible controls of the same length yield a better
val when starting in the same x:

-- > OptCtrlSeq : (x : X) -> (n : Nat) -> CtrlSeq x n -> Type
-- > OptCtrlSeq x n ys = (ys' : CtrlSeq x n) -> so (val x n ys' <= val x n ys)

> OptCtrlSeq : CtrlSeq x n -> Type
> OptCtrlSeq {x} {n} ys = (ys' : CtrlSeq x n) -> so (val ys' <= val ys)

Sanity check: () is optimal control sequence

-- > oneIsOptCtrlSeq : (x : X) -> OptCtrlSeq x Z ()
-- > oneIsOptCtrlSeq x () = reflexive_Float_lte 0

> nilIsOptCtrlSeq : (x : X) -> OptCtrlSeq {x} Nil
> nilIsOptCtrlSeq x ys' = reflexive_Float_lte 0

# S1103

It is easy to compute sequences of feasible controls if one has a rule
that tells one which (feasible) control to select when in a given
state. Such rules are called policies

> Policy : Type
> Policy = (x : X) -> Y x

Sequences of policies of length n can be represented by values of
type |Vect Policy n|: 

> PolicySeq : Nat -> Type
> PolicySeq n = Vect n Policy

Given one such sequences, the corresponding sequence of controls is

> %assert_total
> ctrl : (x : X) -> PolicySeq n -> CtrlSeq x n
> ctrl x Nil = Nil
> ctrl x (p :: ps) = (p x :: ctrl (step x (p x)) ps)

If |X| is in |ReflDecEq|, given a sequence of policies |ps| and a
sequence of controls |ys| of the same length, one can construct a new
policy sequence |ps'| whose corresponding controls are |ys|. This
construction is crucial for proving that sequences of controls obtained
from optimal policy sequences are optimal, see below.

> %assert_total
> modifyPolicySeq : (DecEq.DecEq X) => 
>                   PolicySeq n -> 
>                   CtrlSeq x n -> 
>                   PolicySeq n

> modifyPolicySeq {n = Z} Nil Nil = Nil

> modifyPolicySeq {n = S m} {x = x} (p :: ps) (y :: ys) = 
>    let ps' = modifyPolicySeq ps ys in
>      modifyDepFun p (x ** y) :: ps'

> %assert_total
> modifyPolicySeqLemma : (ReflDecEq X) =>
>                        (ps : PolicySeq n) -> 
>                        (ys : CtrlSeq x n) ->
>                        ctrl x (modifyPolicySeq ps ys) = ys

> modifyPolicySeqLemma Nil Nil = refl

> modifyPolicySeqLemma {x} {n = S m} (p :: ps) (y :: ys) = foo where
>   ps'  :  PolicySeq m
>   ps'  =  modifyPolicySeq ps ys
>   s1   :  ctrl (step x y) ps' = ys
>   s1   =  modifyPolicySeqLemma ps ys
>   p'   :  Policy 
>   p'   =  modifyDepFun p (x ** y)
>   s2   :  p' x = y
>   s2   =  modifyDepFunLemma p (x ** y)
>   s3   :  p' :: ps' = modifyPolicySeq (p :: ps) (y :: ys) -- = p' :: ps'
>   s3   =  refl
>   s4   :  ctrl x (p' :: ps') = (p' x) :: ctrl (step x (p' x)) ps'
>   s4   =  refl
>   s5   :  (p' x) :: ctrl (step x (p' x)) ps' = y :: ctrl (step x y) ps'
>   s5   =  replace  {a = Y x}
>                    {x = p' x}
>                    {P = \ z => (p' x) :: ctrl (step x (p' x)) ps'  = 
>                                z      :: ctrl (step x z) ps'} s2 refl
>   s6   :  y :: ctrl (step x y) ps' = y :: ys
>   -- s6   =  replace {a = CtrlSeq (step x y) m}
>   --                 {x = ctrl (step x y) ps'}
>   --                 {P = \ z => y :: ctrl (step x y) ps' = y :: z} s1 refl
>   s6   =  rewrite s1 in refl
>   s7   :  ctrl x (p' :: ps') = y :: ys   
>   s7   =  trans (trans s4 s5) s6
>   foo  :  ctrl x (modifyPolicySeq (p :: ps) (y :: ys)) = y :: ys
>   foo  =  replace  {a = PolicySeq (S m)}
>                    {x = p' :: ps'}
>                    {y = modifyPolicySeq (p :: ps) (y :: ys)}
>                    {P = \ z => ctrl x z = y :: ys} s3 s7

The value (in terms of cumulated rewards) of a sequence of policies is
given by: 

> %assert_total
> Val : (x : X) -> PolicySeq n -> Float
> Val {n = Z} _ _ = 0
> Val {n = S m} x (p :: ps) = reward x (p x) x' + Val x' ps where
>   x' : X  
>   x' = step x (p x)

It is easy to prove 

Val x ps = val (ctrl x ps)

Base case: 
  Val x Nil = val (ctrl x Nil)

  Val x Nil
    = {- def. of Val -}
  0
    = {- def. of val -}
  val Nil
    = {- def. of ctrl -}
  val (ctrl x Nil)

Induction step: 
  Val x ps = val (ctrl x ps) 
    => 
  Val x (p :: ps) = val (ctrl x (p :: ps))

  Val x (p :: ps)
    = {- def. of Val with y = p x, x' = step x y -}
  reward x y x' + Val x' ps
    = {- induction hypothesis -}
  reward x y x' + val (ctrl x' ps)
    = {- def. of val -}
  val (y :: (ctrl x' ps))
    = {- def. of y, x', ctrl -}
  val (ctrl x (p :: ps))

We can implement the proof in Idris and (type) check its correctness:

> %assert_total
> valValLemma : (x : X) ->
>               (ps : PolicySeq n) -> 
>               Val x ps = val (ctrl x ps)

> valValLemma _ Nil = refl

> valValLemma x (p :: ps) = step4 where
>   y : Y x
>   y = p x
>   x' : X
>   x' = step x y
>   ih : Val x' ps = val (ctrl x' ps)
>   ih = valValLemma x' ps
>   step1 : Val x (p :: ps) = reward x y x' + Val x' ps
>   step1 = refl
>   step2 : Val x (p :: ps) = reward x y x' + val (ctrl x' ps)
>   step2 = replace {P = \ z => Val x (p :: ps) = reward x y x' + z} ih step1
>   -- a = b && x = y + a => x = y + b
>   step3 : reward x y x' + val (ctrl x' ps) = val (ctrl x (p :: ps))
>   step3 = refl
>   step4 : Val x (p :: ps) = val (ctrl x (p :: ps))
>   step4 = trans step2 step3

> valValLemma' : (ps' : PolicySeq n) -> 
>                (ps : PolicySeq n) -> 
>                (x : X) ->
>                so (Val x ps' <= Val x ps) -> 
>                so (val (ctrl x ps') <= val (ctrl x ps))

> valValLemma' ps' ps x o = l2 where
>    l1  : so (val (ctrl x ps') <= Val x ps)
>    l1  = replace {P = \ z => so (z <= Val x ps)} (valValLemma x ps') o
>    l2  : so (val (ctrl x ps') <= val (ctrl x ps))
>    l2  = replace {P = \ z => so (val (ctrl x ps') <= z)} (valValLemma x ps) l1

The notion of optimal sequence of policies:

> OptPolicySeq : (n : Nat) -> PolicySeq n -> Type
> OptPolicySeq n ps = (x : X) -> 
>                     (ps' : PolicySeq n) -> 
>                     so (Val x ps' <= Val x ps)

(Sanity check: Nil is optimal

> nilIsOptPolicySeq : OptPolicySeq Z Nil
> nilIsOptPolicySeq x ps' = reflexive_Float_lte 0

) is interesting because of the following lemma:

> OptLemma : (ReflDecEq X) =>
>            (n : Nat) -> 
>            (ps : PolicySeq n) -> 
>            OptPolicySeq n ps ->
>            (x : X) ->
>            OptCtrlSeq (ctrl x ps)

> OptLemma n ps o x ys' = r  where
  
1. construct ps' s.t. ctrl x ps' = ys'

>    ps' : PolicySeq n
>    ps' = modifyPolicySeq ps ys'
>    m   : ctrl x ps' = ys'
>    m   = modifyPolicySeqLemma ps ys'

2. apply o to deduce Val x ps' <= Val x ps

>    o'  : so (Val x ps' <= Val x ps)
>    o'  = o x ps'
>    l2  : so (val (ctrl x ps') <= val (ctrl x ps))
>    l2  = valValLemma' ps' ps x o'

3. conclude by applying valVal that val ys' <= val (ctrl x ps)

>    l3  : val (ctrl x ps') = val ys'
>    l3  = replace  {a = CtrlSeq x n}
>                   {x = ctrl x ps'}
>                   {y = ys'}
>                   {P = \z => val (ctrl x ps') = val z} m refl
>    r   : so (val ys' <= val (ctrl x ps))
>    r   = replace {P = \ z => so (z <= val (ctrl x ps))} l3 l2

|OptLemma| ensures that optimal control sequences can be computed from
optimal sequences of policies. This is particularly useful because, as
we will see in 'S1105', optimal sequences of policies can be computed
efficiently via Bellman's backwards induction algorithm.

# S1104

...

# S1105

...

# The computation:

> {-

> nSteps : Nat
> nSteps = 5

> ps : PolicySeq nSteps
> ps = backwardsInduction nSteps

> controls : (n : Nat) -> X -> Vect Policy n -> Vect Action n
> controls Z _ _  = Nil
> controls (S m) x (p :: ps) = 
>   ((getWitness (p x)) :: (controls m (step x (p x)) ps))

> x0 : X
> x0 = (0 ** oh)

> as : Vect Action nSteps
> as = controls nSteps x0 ps

> main : IO ()
> main = putStrLn (show as)

> -}
