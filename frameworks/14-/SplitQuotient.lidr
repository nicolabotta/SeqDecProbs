> module SplitQuotient

> import Syntax.PreorderReasoning
> import KernelQuotient as KQ

> %default total

Given a type |Base| and a binary relation |~| on Base:

 |(~) : Base -> Base -> Type|

we want to build a type that can be considered the
quotient of |Base| by the smallest equivalence relation
that contains |~|.

If we have a function |normalize: Base -> Base| 

that maps any |x| to an element related to |x|, i.e.

 |(x : Base) -> normalize x ~ x|

and maps any two related elements to the same, i.e.

 |(x, y : Base) -> x ~ y -> normalize x = normalize y|

it follows that 

 |normalize| is idempotent and

 |ker normalize| is (the propositional truncation of)
 the smallest equivalence relation containing |~|, so
 the construction in KernelQuotient fits the bill.

------------------------------------------------------------
module parameters

> Base : Type
> Relation : Base -> Base -> Type
>
> syntax [x] "~" [y] = Relation x y
>
> normalize : Base -> Base
>
> normalizeMapsRelatedToEQ : 
>   (x, y : Base) ->
>   (x ~ y) ->
>   SplitQuotient.normalize x = SplitQuotient.normalize y
>
> normalizeIsRelated :
>   (x : Base) ->
>   (normalize x) ~ x

------------------------------------------------------------
define parameters of the imported module KernelQuotient

> KQ.KBase = Base
> KQ.normalize = SplitQuotient.normalize
> KQ.normalizeIdem x = 
>   normalizeMapsRelatedToEQ 
>       (KQ.normalize x) 
>       x 
>       (normalizeIsRelated x)

> Quot : Type
> Quot = KQ.KQuot

------------------------------------------------------------

> ||| The classes of related elements are equal
> |||
> classOfEqIfRelated : (x, y : Base) ->
>                      (x ~ y) ->
>                      [x] = [y]
>
> classOfEqIfRelated x y xRely = 
>   classOfEqIfNormalizeEq x y 
>             (normalizeMapsRelatedToEQ x y xRely)

> ||| any |~|-invariant function maps |x| and |normalize x|
> ||| to the same value
> |||
> invNormalizeEq : {B : Type} ->
>                  (f : Base -> B) ->
>                  (fInv : (x, x' : Base) ->
>                          (x ~ x') ->
>                          f x = f x'
>                  ) ->
>                  (x : Base) ->
>                  f (KQ.normalize x) = f x
>
> invNormalizeEq f fInv x = 
>   fInv (KQ.normalize x) x (normalizeIsRelated x)

> ||| |~|-invariant functions are |ker normalize|-invariant
> |||
> invToInvN : {B : Type} ->
>             (f : Base -> B) ->
>             (fInv : (x, x' : Base) ->
>                     (x ~ x') ->
>                     (f x = f x')
>             ) ->
>             (x, x' : Base) ->
>             (KQ.normalize x = KQ.normalize x') ->
>             (f x = f x')
>
> invToInvN f fInv x y nxEQny = 
>     (f x)                 ={ sym (invNormalizeEq f fInv x) }= 
>     (f (KQ.normalize x))  ={ cong nxEQny                   }=
>     (f (KQ.normalize y))  ={ invNormalizeEq f fInv y       }=
>     (f y)                 QED

> ||| computation rule for lift of |~|-invariant functions
> |||
> liftCompR : {B : Type} ->
>             (f : Base -> B) ->
>             (fInv : (x, x' : Base) ->
>                     (x ~ x') ->
>                     (f x = f x')
>             ) ->
>             (x : Base) ->
>             (lift f) [x] = f x
>
> liftCompR f fInv x = liftComp f (invToInvN f fInv) x 

> ||| |~|-invariant binary functions map |(normalize x, normalize y)|
> ||| and |(x, y)| to the same value
> invNormalizeEq2 : {B : Type} ->
>                   (f : Base -> Base -> B) ->
>                   (fInv : (x, x' : Base) ->
>                           (x ~ x' ) ->
>                           (y, y' : Base) ->
>                           (y ~ y') ->
>                           f x y = f x' y'
>                   ) ->
>                   (x, y : Base) ->
>                   f (KQ.normalize x) (KQ.normalize y) = f x y
>
> invNormalizeEq2 f fInv x y = 
>   fInv  (KQ.normalize x) x (normalizeIsRelated x)
>         (KQ.normalize y) y (normalizeIsRelated y)

> ||| binary |~|-invariant functions are |ker normalize|-invariant
> invToInvN2 : {B : Type} ->
>              (f : Base -> Base -> B) ->
>              (fInv : (x, x' : Base) ->
>                      (x  ~ x' ) ->
>                      (y, y' : Base) ->
>                      (y ~ y') ->
>                      (f x y = f x' y')
>              ) ->
>              (x, x' : Base) ->
>              (KQ.normalize x = KQ.normalize x' ) ->
>              (y, y' : Base) ->
>              (KQ.normalize y = KQ.normalize y') ->
>              (f x y) = (f x' y')
>
> invToInvN2 f fInv x x' nxEQnx' y y' nyEQny' = 
>     (f x y)           
>       ={ sym (invNormalizeEq2 f fInv x y) }= 
>     (f (KQ.normalize x) (KQ.normalize y))  
>       ={ cong {f = \ z => f z (KQ.normalize y)} nxEQnx'  }=
>     (f (KQ.normalize x') (KQ.normalize y))  
>       ={ cong {f = \ z => f (KQ.normalize x') z} nyEQny' }=
>     (f (KQ.normalize x') (KQ.normalize y'))  
>       ={ invNormalizeEq2 f fInv x' y'                  }=
>     (f x' y')              
>       QED

> ||| computation rule for lift2 of |~|-invariant binary functions
> lift2CompR : {B : Type} ->
>              (f : Base -> Base-> B) ->
>              (fInv : (x, x' : Base) ->
>                      (x  ~ x' ) ->
>                      (y, y' : Base) ->
>                      (y ~ y') ->
>                      (f x y = f x' y')
>              ) ->
>              (x, y : Base) ->
>              (lift2 f) [x] [y] = f x y
>
> lift2CompR f fInv x y = lift2Comp f (invToInvN2 f fInv) x y


> ||| For a |~|-invariant binary operation |op|,
> ||| |liftBinOp op| is (the currying of) a lift of (the 
> ||| uncurrying of) |op| in the sense that this diagram commutes:
> |||
> |||                 uncurry (liftBinop op)
> |||        Quot x Quot ------------------> Quot
> |||             ^                           ^
> |||   [_] x [_] |                           | [_]
> |||             |                           |
> |||        Base x Base ------------------> Base
> |||                       uncurry op
> ||| 
> ||| This can be seen as a "computation rule" for
> ||| |liftBinop op|: |(liftBinop op) [x] [y] = [x `op` y]|.
> |||
> liftBinopCompR: (op : Base -> Base -> Base) ->
>                 (opInv : (x, x' : Base) ->
>                          (x ~ x') ->
>                          (y, y' : Base) ->
>                          (y ~ y') ->
>                          (x `op` y) ~ (x' `op` y')
>                 ) ->
>                 (x, y : Base) ->
>                 (liftBinop op) [x] [y] = [x `op` y]
>
> liftBinopCompR op opInv x y =
>   lift2CompR {B=Quot} (classOfAfterOp op) opInv' x y where
>   opInv' :  (x, x' : Base) ->
>             (x ~ x') -> 
>             (y, y' : Base) ->
>             (y ~ y') -> 
>             [x `op` y] = [x' `op` y']
>   opInv' x x' xRx' y y' yRy' = 
>     classOfEqIfRelated (x `op` y) (x' `op` y') 
>                        (opInv x x' xRx' y y' yRy')

