> module SplitQuotient -- originally implemented by Tim Richter (Dec. 2015)

> import Syntax.PreorderReasoning

> import KernelQuotient as KQ


> %default total


Consider a type |Base| and a binary relation |~| on Base:

 |(~) : Base -> Base -> Type|

We want to build a type that can be considered the
quotient of |Base| by the smallest equivalence relation
that contains |~|.

If we have a function |normalize: Base -> Base| 
picking a representative

that maps any |x| to an element related to |x|, i.e.

 |(x : Base) -> normalize x ~ x|

and maps any two related elements to the same, i.e.

 |(x, y : Base) -> x ~ y -> normalize x = normalize y|

it follows that 

 |normalize| is idempotent and

 |ker normalize| is (the propositional truncation of)
 the smallest equivalence relation containing |~|, so
 the construction in KernelQuotient fits the bill.

----------------------------------------------------------
module parameters

> Base : Type
> Relation : SplitQuotient.Base -> SplitQuotient.Base -> Type
>
> syntax [x] "~" [y] = Relation x y
>
> normalize : SplitQuotient.Base -> SplitQuotient.Base
>
> normalizeMapsRelatedToEQ : 
>   (x, y : SplitQuotient.Base) ->
>   (x ~ y) ->
>   SplitQuotient.normalize x = SplitQuotient.normalize y
>
> normalizeIsRelated :
>   (x : SplitQuotient.Base) ->
>   (normalize x) ~ x

--------------------------------------------------------------

> KQ.KBase = SplitQuotient.Base
> KQ.normalize = SplitQuotient.normalize
> KQ.normalizeIdem x = 
>   normalizeMapsRelatedToEQ 
>       (KQ.normalize x) 
>       x 
>       (normalizeIsRelated x)

> Quot : Type
> Quot = KQ.KQuot

> ||| The classes of related elements are equal
> |||
> classOfEqIfRelated :  (x, y : Base) ->
>                       (x ~ y) ->
>                       [x] = [y]
>
> classOfEqIfRelated x y xRely = classOfEqIfNormalizeEq x y nxEQny where
>   nxEQny : KQ.normalize x = KQ.normalize y
>   nxEQny = normalizeMapsRelatedToEQ x y xRely


> invNormalizeEq :  {B : Type} ->
>                   (f : SplitQuotient.Base -> B) ->
>                   ( (x, x' : SplitQuotient.Base) ->
>                     (x ~ x') ->
>                     f x = f x'
>                   ) ->
>                   (x : SplitQuotient.Base) ->
>                   f (KQ.normalize x) = f x
> invNormalizeEq f fInv x = fInv (KQ.normalize x) x (normalizeIsRelated x)


> invToInvN : {B : Type} ->
>             (f : SplitQuotient.Base -> B) ->
>             ( (x, x' : SplitQuotient.Base) ->
>               (x ~ x') ->
>               (f x = f x')
>             ) ->
>             (x, x' : SplitQuotient.Base) ->
>             (KQ.normalize x = KQ.normalize x') ->
>             (f x = f x')
>
> invToInvN f fInv x y nxEQny = 
>     (f x)                 ={ sym (invNormalizeEq f fInv x) }= 
>     (f (KQ.normalize x))  ={ cong nxEQny                   }=
>     (f (KQ.normalize y))  ={ invNormalizeEq f fInv y       }=
>     (f y)              QED


> liftCompR : {B : Type} ->
>             (f : SplitQuotient.Base -> B) ->
>             ( (x, x' : SplitQuotient.Base) ->
>               (x ~ x') ->
>               (f x = f x')
>             ) ->
>             (x : SplitQuotient.Base) ->
>             (lift f) [x] = f x
>
> liftCompR f fInv x = liftComp f (invToInvN f fInv) x 

> invNormalizeEq2 : {B : Type} ->
>             (f : SplitQuotient.Base -> SplitQuotient.Base -> B) ->
>             ( (x, x' : SplitQuotient.Base) ->
>               (x ~ x' ) ->
>               (y, y' : SplitQuotient.Base) ->
>               (y ~ y') ->
>               f x y = f x' y'
>             ) ->
>             (x, y : SplitQuotient.Base) ->
>             f (KQ.normalize x) (KQ.normalize y) = f x y
> invNormalizeEq2 f fInv x y = 
>   fInv  (KQ.normalize x) x (normalizeIsRelated x)
>         (KQ.normalize y) y (normalizeIsRelated y)

> invToInvN2 :  {B : Type} ->
>               (f : SplitQuotient.Base -> SplitQuotient.Base -> B) ->
>               ( (x, x' : SplitQuotient.Base) ->
>                 (x  ~ x' ) ->
>                 (y, y' : SplitQuotient.Base) ->
>                 (y ~ y') ->
>                 (f x y = f x' y')
>               ) ->
>               (x, x' : SplitQuotient.Base) ->
>               (KQ.normalize x = KQ.normalize x' ) ->
>               (y, y' : SplitQuotient.Base) ->
>               (KQ.normalize y = KQ.normalize y') ->
>               (f x y) = (f x' y')
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


> lift2CompR :  {B : Type} ->
>               (f : SplitQuotient.Base -> SplitQuotient.Base-> B) ->
>               ( (x, x' : SplitQuotient.Base) ->
>                 (x  ~ x' ) ->
>                 (y, y' : SplitQuotient.Base) ->
>                 (y ~ y') ->
>                 (f x y = f x' y')
>               ) ->
>               (x, y : SplitQuotient.Base) ->
>               (lift2 f) [x] [y] = f x y
>
> lift2CompR f fInv x y = lift2Comp f (invToInvN2 f fInv) x y


> ||| For a ~-invariant binary operation |op|,
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
> liftBinopCompR: (op : SplitQuotient.Base -> SplitQuotient.Base -> SplitQuotient.Base) ->
>                 ( (x, x' : SplitQuotient.Base) ->
>                   (x ~ x') ->
>                   (y, y' : SplitQuotient.Base) ->
>                   (y ~ y') ->
>                   (x `op` y) ~ (x' `op` y')
>                 ) ->
>                 (x, y : SplitQuotient.Base) ->
>                 (liftBinop op) [x] [y] = [x `op` y]
>
> liftBinopCompR op opInv x y =
>   lift2CompR {B=SplitQuotient.Quot} (classOfAfterOp op) opInv' x y where
>   opInv' :  (x, x' : SplitQuotient.Base) ->
>             (x ~ x') -> 
>             (y, y' : SplitQuotient.Base) ->
>             (y ~ y') -> 
>             [x `op` y] = [x' `op` y']
>   opInv' x x' xRx' y y' yRy' = classOfEqIfRelated (x `op` y) (x' `op` y') 
>                                (opInv x x' xRx' y y' yRy')

> liftBinopCompR1 : (op : SplitQuotient.Base -> SplitQuotient.Base -> SplitQuotient.Base) ->
>                 ( (x, x' : SplitQuotient.Base) ->
>                   (x ~ x') ->
>                   (y, y' : SplitQuotient.Base) ->
>                   (y ~ y') ->
>                   (x `op` y) ~ (x' `op` y')
>                 ) ->
>                 (x, y : SplitQuotient.Quot) ->
>                 (liftBinop op) x y = [(repr x) `op` (repr y)]
>
> liftBinopCompR1 op opInv x y = 
>   let rx = KQ.repr x in
>   let ry = KQ.repr y in
>   ((liftBinop op)  x    y  ) ={ cong {f = \z => (liftBinop op) z y}    (sym (KQ.classOfAfterReprIsId x)) }=
>   ((liftBinop op) [rx]  y  ) ={ cong {f = \z => (liftBinop op) [rx] z} (sym (KQ.classOfAfterReprIsId y)) }=
>   ((liftBinop op) [rx] [ry]) ={ liftBinopCompR op opInv rx ry                                            }=
>   ([rx `op` ry])             QED


----------------------------
Type classes
----------------------------

 instance Num SplitQuotient.Base => Num SplitQuotient.Quot where
   (+) = liftBinop (+)
   (*) = liftBinop (*)
   fromInteger = classOf . fromInteger
   -- abs = classOf . (lift abs)

 instance Show SplitQuotient.Base => Show SplitQuotient.Quot where
   show (Class x _) = "[" ++ show x ++ "]"

 instance DecEq SplitQuotient.Base => DecEq SplitQuotient.Quot where
   decEq (Class x nxIsx) (Class y nyIsy)
     with (decEq (SplitQuotient.normalize x) (SplitQuotient.normalize y))
     | (Yes p) = Yes (classesEqIfReprEq  (Class x nxIsx)
                                         (Class y nyIsy)
                                         xIsy) where
         xIsy =
           (x)             ={ sym nxIsx }=
           (SplitQuotient.normalize x)   ={ p }=
           (SplitQuotient.normalize y)   ={ nyIsy }=
           (y)             QED
     | (No contra) = No (contra . (cong {f = SplitQuotient.normalize . repr}))

