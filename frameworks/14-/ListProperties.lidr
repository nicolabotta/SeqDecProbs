> module ListProperties

> import Data.List
> import Data.List.Quantifiers
> import Data.Fin
> import Control.Isomorphism
> import Syntax.PreorderReasoning

> import ListOperations
> import FunOperations
> import FunProperties
> import Unique
> import Finite
> import FiniteOperations
> import Sigma
> import PairsOperations
> import Basics
> import IsomorphismOperations
> import FinProperties
> import VoidProperties
> import UnitProperties
> import NumRefinements
> import PairProperties


> %default total
> %auto_implicits off
> -- %access export
> %access public export


* |List| is a functor:

> -- functorSpec1 : fmap . id = id

> -- functorSpec2 : fmap (f . g) = (fmap f) . (fmap g)


* |List| is a monad:

> -- monadSpec1 : (fmap f) . ret = ret . f

> -- monadSpec21 : bind (ret a) f = f a

> -- monadSpec22 : bind ma ret = ma

> -- monadSpec23 : {A, B, C : Type} -> {f : A -> M B} -> {g : B -> M C} ->
> --                bind (bind ma f) g = bind ma (\ a => bind (f a) g)


* |List| is a container monad:

> |||
> elemNonEmptySpec0 : {A : Type} ->
>                     (a : A) -> (as : List A) ->
>                     a `Elem` as -> ListOperations.NonEmpty as
> elemNonEmptySpec0 _  Nil      p = absurd p
> elemNonEmptySpec0 _ (a :: as) _ = ()


> |||
> elemNonEmptySpec1 : {A : Type} ->
>                     (as : List A) ->
>                     ListOperations.NonEmpty as -> Sigma A (\ a => a `Elem` as)
> elemNonEmptySpec1  Nil      c = void c
> elemNonEmptySpec1 (a :: as) _ = MkSigma a Here 

> |||
> containerMonadSpec1 : {A : Type} -> {a : A} -> a `Elem` (ret a)
> containerMonadSpec1 {A} {a} = Here

> -- containerMonadSpec2 : {A : Type} -> (a : A) -> (ma : M A) -> (mma : M (M A)) ->
> --                       a `Elem` ma -> ma `Elem` mma -> a `Elem` (join mma)

> containerMonadSpec3 : {A : Type} -> {P : A -> Type} -> (a : A) -> (as : List A) ->
>                       All P as -> a `Elem` as -> P a
> containerMonadSpec3 a'  Nil       _           eprf        = absurd eprf
> containerMonadSpec3 a' (a :: as)  Nil         _           impossible
> containerMonadSpec3 a  (a :: as) (pa :: pas)  Here        = pa
> containerMonadSpec3 a' (a :: as) (pa :: pas) (There eprf) = containerMonadSpec3 a' as pas eprf


> -- containerMonadSpec4 : {A : Type} -> (ma : M A) -> fmap outl (tagElem ma) = ma


* Specific container monad properties

> |||
> uniqueAllLemma : {A : Type} -> {P : A -> Type} -> 
>                  Unique1 P -> (as : List A) -> Unique (All P as)
> uniqueAllLemma u1P  Nil      Nil Nil = Refl
> uniqueAllLemma u1P (a :: as) (pa :: pas) (pa' :: pas') = 
>     ( pa :: pas )
>   ={ replace {P = \ ZUZU => pa :: pas = ZUZU :: pas} (u1P a pa pa') Refl }=
>     ( pa' :: pas )
>   ={ replace {P = \ ZUZU => pa' :: pas = pa' :: ZUZU} (uniqueAllLemma u1P as pas pas') Refl }=
>     ( pa' :: pas' ) 
>   QED   


> ||| 
> finiteAllLemma0 : {A : Type} -> {P : A -> Type} -> 
>                   Finite1 P -> Iso (All P Nil) Unit
> finiteAllLemma0 f1P = MkIso to from toFrom fromTo where
>   to : All P Nil -> Unit
>   to Nil = () 
>   from : Unit -> All P Nil
>   from () = Nil
>   toFrom : (k : Unit) -> to (from k) = k
>   toFrom () = Refl
>   fromTo : (nil : All P Nil) -> from (to nil) = nil
>   fromTo Nil = Refl


> |||
> finiteAllLemma1 : {A : Type} -> {P : A -> Type} -> 
>                   Finite1 P -> (a : A) -> (as : List A) -> 
>                   Iso (All P (a :: as)) (P a, All P as)
> finiteAllLemma1 {P} f1P a as = MkIso to from toFrom fromTo where
>   to : All P (a :: as) -> (P a, All P as)
>   to (pa :: pas) = (pa, pas)
>   from : (P a, All P as) -> All P (a :: as)
>   from (pa, pas) = pa :: pas
>   toFrom : (papas : (P a, All P as)) -> to (from papas) = papas
>   toFrom (pa, pas) = Refl
>   fromTo : (papas : All P (a :: as)) -> from (to papas) = papas
>   fromTo (pa :: pas) = Refl


> |||
> finiteAllLemma : {A : Type} -> {P : A -> Type} -> 
>                  Finite1 P -> (as : List A) -> Finite (All P as)
> finiteAllLemma {P} f1P Nil = MkSigma (S Z) iso where
>   iso : Iso (All P Nil) (Fin (S Z))
>   iso = isoTrans (finiteAllLemma0 f1P) (isoSym isoFin1Unit)
> finiteAllLemma {P} f1P (a :: as) = MkSigma n iso where
>   fH : Finite (P a)
>   fH = f1P a
>   mH : Nat
>   mH = getWitness fH
>   isoH : Iso (P a) (Fin mH)
>   isoH = getProof fH
>   fT : Finite (All P as)
>   fT = finiteAllLemma f1P as
>   mT : Nat
>   mT = getWitness fT
>   isoT : Iso (All P as) (Fin mT)
>   isoT = getProof fT
>   n  : Nat
>   n  = mH * mT
>   iso1 : Iso (All P (a :: as)) (P a, All P as)
>   iso1 = finiteAllLemma1 f1P a as
>   iso2 : Iso (P a, All P as) (Fin mH, Fin mT)
>   iso2 = pairCong isoH isoT
>   iso3 : Iso (Fin mH, Fin mT) (Fin (mH * mT))
>   iso3 = finPairTimes
>   iso  : Iso (All P (a :: as)) (Fin n)
>   iso  = isoTrans iso1 (isoTrans iso2 iso3)


> |||
> finiteAll : {A : Type} -> {P : A -> Type} -> 
>             Finite1 P -> (as : List A) -> Finite (All P as)
> finiteAll = finiteAllLemma


> ||| NotEmpty is finite
> finiteNonEmpty : {A : Type} -> (as : List A) -> Finite (ListOperations.NonEmpty as)
> finiteNonEmpty  Nil      = finiteVoid
> finiteNonEmpty (a :: as) = finiteUnit

> tagElemPreservesLength : {A : Type} -> (as : List A) -> length (tagElem as) = length as
> tagElemPreservesLength  Nil      = Refl
> tagElemPreservesLength (a :: as) = ( length (tagElem (a :: as)) )
>                                  ={ Refl }=
>                                    ( length ((MkSigma a Here) :: (map (idThere a as) (tagElem as))) )
>                                  ={ Refl }=
>                                    ( S (length (map (idThere a as) (tagElem as))) )
>                                  ={ cong (mapPreservesLength (idThere a as) (tagElem as)) }=
>                                    ( S (length (tagElem as)) )
>                                  ={ cong (tagElemPreservesLength as) }=
>                                    ( S (length as) )  
>                                  ={ Refl }=
>                                    ( length (a :: as) )
>                                  QED


* Fusion-related properties:

> ||| 
> mapSndMapCrossAnyIdLemma : {A, B, C : Type} -> 
>                            (f : A -> C) -> 
>                            (abs : List (A, B)) -> 
>                            map snd (map (cross f id) abs) = map snd abs
> mapSndMapCrossAnyIdLemma _ Nil = Refl
> mapSndMapCrossAnyIdLemma f ((a, b) :: abs) = 
>     ( map snd (map (cross f id) ((a, b) :: abs)) )
>   ={ Refl }=
>     ( map snd ((f a, b) :: map (cross f id) abs) )
>   ={ Refl }=
>     ( b :: map snd (map (cross f id) abs) )
>   ={ cong (mapSndMapCrossAnyIdLemma f abs) }=
>     ( b :: map snd abs )
>   ={ Refl }=
>     ( map snd ((a, b) :: abs) )
>   QED


* Properties of |length|:

> |||
> lengthLemma : {A, B, C : Type} -> 
>               (as : List A) -> (f : A -> B) -> (g : A -> C) ->
>               length (map f as) = length (map g as)
> lengthLemma  Nil      f g = Refl
> lengthLemma (a :: as) f g = ( length (map f (a :: as)) )
>                           ={ Refl }=
>                             ( length (f a :: map f as) )
>                           ={ Refl }=
>                             ( S (length (map f as)) )
>                           ={ cong (lengthLemma as f g) }=
>                             ( S (length (map g as)) )
>                           ={ Refl }=
>                             ( length (g a :: map g as) )
>                           ={ Refl }=
>                             ( length (map g (a :: as)) )
>                           QED


> |||
> lengthConsLemma : {A, B : Type} ->
>                   (a : A) -> (b : B) -> (as : List A) -> (bs : List B) ->
>                   length (a :: as) = length (b :: bs) -> length as = length bs
> lengthConsLemma a b as bs prf = succInjective (length as) (length bs) s2 where
>   s1 : length (a :: as) = length (b :: bs)
>   s1 = prf
>   s2 : S (length as) = S (length bs)
>   s2 = replace2 {P = \ X => \ Y => X = Y} Refl Refl s1


> |||
> lengthReplicateLemma : {A : Type} -> 
>                        (n : Nat) -> (a : A) -> 
>                        length (replicate n a) = n
> lengthReplicateLemma  Z    _ = Refl
> lengthReplicateLemma (S m) a = ( length (replicate (S m) a) )
>                              ={ Refl }=
>                                ( length (a :: replicate m a) )
>                              ={ Refl }=
>                                ( S (length (replicate m a)) )
>                              ={ cong (lengthReplicateLemma m a) }=
>                                ( S m )
>                              QED


* Properties of |zip| and |unzip|:

> |||
> unzipConsLemma : {A, B : Type} -> 
>                  (ab : (A, B)) -> (abs : List (A, B)) ->
>                  unzip (ab :: abs) = (fst ab :: fst (unzip abs), snd ab :: snd (unzip abs))
> unzipConsLemma (a, b) abs with (unzip abs)
>   | (_, _) = Refl

> |||
> fstUnzipConsLemma : {A, B : Type} -> 
>                     (ab : (A, B)) -> (abs : List (A, B)) ->
>                     fst (unzip (ab :: abs)) = fst ab :: fst (unzip abs)
> fstUnzipConsLemma ab abs = cong {f = fst} (unzipConsLemma ab abs)

> |||
> sndUnzipConsLemma : {A, B : Type} -> 
>                     (ab : (A, B)) -> (abs : List (A, B)) ->
>                     snd (unzip (ab :: abs)) = snd ab :: snd (unzip abs)
> sndUnzipConsLemma ab abs = cong {f = snd} (unzipConsLemma ab abs)

> |||
> unzipZipLemma : {A, B : Type} -> 
>                 (as : List A) -> (bs : List B) -> length as = length bs ->
>                 unzip (zip as bs) = (as, bs)
> unzipZipLemma  Nil       Nil      _   = Refl                 
> unzipZipLemma  Nil      (b :: bs) prf = absurd prf
> unzipZipLemma (a :: as)  Nil      prf = absurd (sym prf)
> unzipZipLemma (a :: as) (b :: bs) prf with (unzip (zip as bs)) proof p
>   | (left, right) = s4 where
>       s1 : length as = length bs
>       s1 = lengthConsLemma a b as bs prf
>       s2 : unzip (zip as bs) = (as, bs)
>       s2 = unzipZipLemma as bs s1
>       s3 : (left, right) = (as, bs)
>       s3 = trans p s2
>       s4 : (a :: left, b :: right) = (a :: as, b :: bs)
>       s4 = replace2 {P = \ X => \ Y => (a :: left, b :: right) = (a :: X, b :: Y)} 
>                     (cong {f = fst} s3) (cong {f = snd} s3) Refl

> |||
> sumMapSndUnzipLemma : {A, B : Type} -> (Num B) => 
>                       (abs : List (A, B)) -> sumMapSnd abs = sum (snd (unzip abs))
> sumMapSndUnzipLemma  Nil        = Refl
> sumMapSndUnzipLemma (ab :: abs) = 
>     ( sumMapSnd (ab :: abs) )
>   ={ Refl }=
>     ( sum (map snd (ab :: abs)) )
>   ={ Refl }=
>     ( sum (snd ab :: map snd abs) )
>   ={ Refl }=
>     ( snd ab + sum (map snd abs) )
>   ={ Refl }=
>     ( snd ab + sumMapSnd abs )
>   ={ cong (sumMapSndUnzipLemma abs) }=  
>     ( snd ab + sum (snd (unzip abs)) )
>   ={ Refl }=
>     ( sum (snd ab :: snd (unzip abs)) )
>   ={ cong (sym (sndUnzipConsLemma ab abs)) }=
>     ( sum (snd (unzip (ab :: abs))) )
>   QED    


* Properties of |fold|:

> foldrListLemma : {A, B : Type} -> 
>                  (f : A -> B -> B) -> (e : B) ->
>                  (a : A) -> (as : List A) ->
>                  foldr f e (a :: as) = f a (foldr f e as)
> foldrListLemma f e a as = Refl


* Properties of |sum| (for lists of types which are refinements of |Num|):

> |||
> sumSingletonLemma : {A : Type} -> (NumPlusZeroNeutral A) => (x : A) -> sum [x] = x
> sumSingletonLemma x = ( x + 0 )
>                     ={ plusZeroRightNeutral x }=
>                       ( x )
>                     QED

> |||
> sumPlusAppendLemma : {B : Type} -> (NumPlusAssociative B) => 
>                      (xs : List B) -> (ys : List B) ->
>                      (sum xs + sum ys) = sum (xs ++ ys)
> sumPlusAppendLemma Nil       ys = plusZeroLeftNeutral (sum ys)
> sumPlusAppendLemma (x :: xs) ys =
>     ( sum (x :: xs) + sum ys )
>   ={ Refl }=
>     ( (x + sum xs) + sum ys )
>   ={ sym (plusAssociative x (sum xs) (sum ys)) }=
>     ( x + (sum xs + sum ys) )
>   ={ cong (sumPlusAppendLemma xs ys) }=
>     ( x + sum (xs ++ ys) )
>   ={ Refl }=
>     ( sum (x :: (xs ++ ys)) )
>   ={ Refl }=
>     ( sum ((x :: xs) ++ ys) )
>   QED

> |||
> sumConcatLemma : {B : Type} -> (NumPlusAssociative B) => 
>                  (bss : List (List B)) -> 
>                  sum (map sum bss) = sum (concat bss)
> sumConcatLemma  Nil        = Refl
> sumConcatLemma (bs :: bss) =
>     ( sum (map sum (bs :: bss)) )
>   ={ Refl }=
>     ( sum (sum bs :: map sum bss) )
>   ={ Refl }=
>     ( sum bs + sum (map sum bss) )
>   ={ cong (sumConcatLemma bss) }=
>     ( sum bs + sum (concat bss) )
>   ={ sumPlusAppendLemma bs (concat bss) }=
>     ( sum (bs ++ concat bss) )
>   ={ Refl }=
>     ( sum (concat (bs :: bss)) )
>   QED

> |||
> sumMapSndSingletonLemma : {A, B : Type} -> (NumPlusZeroNeutral B) => 
>                           (a : A) -> (b : B) -> sumMapSnd [(a, b)] = b
> sumMapSndSingletonLemma a b = ( sumMapSnd [(a, b)] )
>                             ={ Refl }=
>                               ( sum (map snd [(a, b)]) )
>                             ={ Refl }=
>                               ( sum [b] )
>                             ={ sumSingletonLemma b }=
>                               ( b )
>                             QED    

> |||
> sumMapSndConcatLemma : {A, B : Type} -> (NumPlusAssociative B) => 
>                        (abss : List (List (A, B))) -> 
>                        sum (map sumMapSnd abss) = sumMapSnd (concat abss)
> sumMapSndConcatLemma  Nil          = Refl 
> sumMapSndConcatLemma (abs :: abss) = 
>     ( sum (map sumMapSnd (abs :: abss)) )
>   ={ Refl }=
>     ( sum (sumMapSnd abs :: map sumMapSnd abss) )
>   ={ Refl }=
>     ( sum (sum (map snd abs) :: map sumMapSnd abss) )
>   ={ Refl }=
>     ( sum (map snd abs) + sum (map sumMapSnd abss) )
>   ={ cong (sumMapSndConcatLemma abss) }=
>     ( sum (map snd abs) + sumMapSnd (concat abss) )
>   ={ Refl }=
>     ( sum (map snd abs) + sum (map snd (concat abss)) )
>   ={ sumPlusAppendLemma (map snd abs) (map snd (concat abss)) }=
>     ( sum (map snd abs ++ map snd (concat abss)) )
>   ={ cong (sym (mapDistributesOverAppend snd abs (concat abss))) }=
>     ( sum (map snd (abs ++ concat abss)) )
>   ={ Refl }=
>     ( sum (map snd (concat (abs :: abss))) )
>   ={ Refl }=
>     ( sumMapSnd (concat (abs :: abss)) )
>   QED

> |||
> sumMapSndMapIdRightMultLemma : {A, B : Type} -> (Num B) => 
>                                (b : B) -> (ab : (A, B)) -> (abs : List (A, B)) -> 
>                                (snd ab) * b + sumMapSnd (mapIdRightMult (abs, b)) 
>                                = 
>                                sumMapSnd (mapIdRightMult ((ab :: abs), b))
> sumMapSndMapIdRightMultLemma b ab abs =
>     ( (snd ab) * b + sumMapSnd (mapIdRightMult (abs, b)) )
>   ={ Refl }=  
>     ( (snd ab) * b + sum (map snd (mapIdRightMult (abs, b))) )
>   ={ Refl }=  
>     ( sum ((snd ab) * b :: (map snd (mapIdRightMult (abs, b)))) )
>   ={ Refl }=  
>     ( sum (snd (fst ab, (snd ab) * b) :: (map snd (mapIdRightMult (abs, b)))) )
>   ={ Refl }=  
>     ( sum (snd ((cross id (* b)) (fst ab, snd ab)) :: (map snd (mapIdRightMult (abs, b)))) )
>   ={ cong {f = \ ZUZU => sum (snd ((cross id (* b)) ZUZU) :: (map snd (mapIdRightMult (abs, b))))} 
>           (sym (pairLemma ab)) }=  
>     ( sum (snd ((cross id (* b)) ab) :: (map snd (mapIdRightMult (abs, b)))) )
>   ={ Refl }=  
>     ( sum (snd ((cross id (* b)) ab) :: (map snd (map (cross id (* b)) abs))) )  
>   ={ Refl }=
>     ( sum (map snd (((cross id (* b)) ab) :: map (cross id (* b)) abs)) )
>   ={ Refl }=  
>     ( sum (map snd (map (cross id (* b)) (ab :: abs))) )
>   ={ Refl }=  
>     ( sum (map snd (mapIdRightMult ((ab :: abs), b))) )
>   ={ Refl }=  
>     ( sumMapSnd (mapIdRightMult ((ab :: abs), b)) )
>   QED

> |||
> mapIdRightMultLemma : {A, B : Type} -> (NumMultDistributesOverPlus B) => 
>                       (absb : (List (A, B), B)) -> 
>                       sumMapSnd (mapIdRightMult absb)
>                       =
>                       (sumMapSnd (fst absb)) * (snd absb)
> mapIdRightMultLemma {A} {B} (Nil, b) = 
>     ( sumMapSnd {A} (mapIdRightMult (Nil, b)) )
>   ={ Refl }=
>     ( sumMapSnd {A} (map (cross id (* b)) Nil) )
>   ={ Refl }=
>     ( sumMapSnd {A} Nil )
>   ={ Refl }=
>     ( 0 )
>   ={ sym (multZeroLeftZero b) }=
>     ( 0 * b )
>   ={ Refl }=     
>     ( (sumMapSnd {A} Nil) * b )
>   ={ Refl }=     
>     ( (sumMapSnd {A} (fst (Nil, b))) * (snd {a = List (A, B)} (Nil, b)) )   
>   QED
> mapIdRightMultLemma ((ab :: abs), b) = assert_total (
>     ( sumMapSnd (mapIdRightMult ((ab :: abs), b)) )
>   ={ sym (sumMapSndMapIdRightMultLemma b ab abs) }=
>     ( (snd ab) * b + sumMapSnd (mapIdRightMult (abs, b)) )
>   ={ cong (mapIdRightMultLemma (abs, b)) }=
>     ( (snd ab) * b + (sumMapSnd (fst (abs, b))) * (snd (abs, b)) )
>   ={ Refl }=
>     ( (snd ab) * b + (sumMapSnd abs) * b )
>   ={ sym (multDistributesOverPlusLeft (snd ab) (sumMapSnd abs) b) }=  
>     ( (snd ab + sumMapSnd abs) * b )
>   ={ Refl }=
>     ( (snd ab + sum (map snd abs)) * b )
>   ={ Refl }=
>     ( (sumMapSnd (ab :: abs)) * b )
>   ={ Refl }=
>     ( (sumMapSnd (fst ((ab :: abs), b))) * (snd ((ab :: abs), b)) )
>   QED
>   )

> |||
> mvMultLemma : {A, A', B : Type} -> (NumMultDistributesOverPlus B) => 
>               (abs : List (A, B)) -> (f : A -> List (A', B)) -> ((a : A) -> sumMapSnd (f a) = 1) ->
>               sumMapSnd (mvMult abs f) = sumMapSnd abs
> mvMultLemma  Nil        _ _   = Refl
> mvMultLemma (ab :: abs) f prf =
>   let a = fst ab in
>   let b = snd ab in
>   let fid = cross f id in
>   let h = mapIdRightMult . fid in
>     ( sumMapSnd (mvMult (ab :: abs) f) )
>   ={ Refl }=
>     ( sumMapSnd (concat (map h (ab :: abs))) )
>   ={ sym (sumMapSndConcatLemma (map h (ab :: abs))) }=
>     ( sum (map sumMapSnd (map h (ab :: abs))) )  
>   ={ Refl }=
>     ( sum (map sumMapSnd (h ab :: map h abs)) )  
>   ={ Refl }=
>     ( sum (sumMapSnd (h ab) :: map sumMapSnd (map h abs)) )
>   ={ cong {f = \ ZUZU => sum (ZUZU :: map sumMapSnd (map h abs))} (mapIdRightMultLemma ((cross f id) ab)) }=
>     ( sum ((sumMapSnd (fst (fid ab))) * (snd (fid ab)) :: map sumMapSnd (map h abs)) )    
>   ={ cong {f = \ ZUZU => sum ((sumMapSnd (fst (fid ab))) * ZUZU :: map sumMapSnd (map h abs))} 
>           (crossAnyIdSndLemma' {ab} {f}) }=
>     ( sum ((sumMapSnd (fst (fid ab))) * (snd ab) :: map sumMapSnd (map h abs)) )
>   ={ cong {f = \ ZUZU => sum ((sumMapSnd ZUZU) * (snd ab) :: map sumMapSnd (map h abs))} 
>           (crossAnyIdFstLemma' {ab} {f}) }=
>     ( sum ((sumMapSnd (f a)) * b :: map sumMapSnd (map h abs)) )
>   ={ cong {f = \ ZUZU => sum (ZUZU * b :: map sumMapSnd (map h abs))} (prf a) }=
>     ( sum (1 * b :: map sumMapSnd (map h abs)) )
>   ={ cong {f = \ ZUZU => sum (ZUZU :: map sumMapSnd (map h abs))} (multOneLeftNeutral b) }=
>     ( sum (b :: map sumMapSnd (map h abs)) )
>   ={ Refl }=
>     ( b + sum (map sumMapSnd (map h abs)) )
>   ={ cong (sumMapSndConcatLemma (map h abs)) }=
>     ( b + sumMapSnd (concat (map h abs)) )
>   ={ Refl }=
>     ( b + sumMapSnd (mvMult abs f) )
>   ={ cong (mvMultLemma abs f prf) }=
>     ( b + sumMapSnd abs )
>   ={ Refl }=  
>     ( b + sum (map snd abs) )
>   ={ Refl }=
>     ( sum (b :: map snd abs) )
>   ={ Refl }=
>     ( sum (map snd (ab :: abs)) )
>   ={ Refl }=
>     ( sumMapSnd (ab :: abs) )
>   QED


* Ad-hoc filtering

> |||
> discardZeroesLemma : {B : Type} -> (NumPlusZeroNeutral B, DecEq B) => 
>                    (bs : List B) -> sum (discardZeroes bs) = sum bs
> discardZeroesLemma  Nil      = Refl
> discardZeroesLemma (b :: bs) with (decEq b 0)
>   | (Yes p) = ( sum (discardZeroes bs) )
>             ={ discardZeroesLemma bs }=
>               ( sum bs )
>             ={ sym (plusZeroLeftNeutral (sum bs)) }=      
>               ( 0 + sum bs )
>             ={ cong {f = \ ZUZU => ZUZU + sum bs} (sym p) }=    
>               ( b + sum bs )
>             ={ Refl }=  
>               ( sum (b :: bs) )
>             QED  
>   | (No _)  = ( sum (b :: discardZeroes bs) )
>             ={ Refl }=
>               ( b + sum (discardZeroes bs) )
>             ={ cong (discardZeroesLemma bs) }=
>               ( b + sum bs )  
>             ={ Refl }=
>               ( sum (b :: bs) )
>             QED

> |||
> discardBySndZeroLemma : {A, B : Type} -> (NumPlusZeroNeutral B, DecEq B) => 
>                         (abs : List (A, B)) -> sumMapSnd (discardBySndZero abs) = sumMapSnd abs
> discardBySndZeroLemma  Nil      = Refl
> discardBySndZeroLemma (ab :: abs) with (decEq (snd ab) 0)
>   | (Yes p) = ( sumMapSnd (discardBySndZero abs) )
>             ={ discardBySndZeroLemma abs }=
>               ( sumMapSnd abs )
>             ={ sym (plusZeroLeftNeutral (sumMapSnd abs)) }=      
>               ( 0 + sumMapSnd abs )
>             ={ cong {f = \ ZUZU => ZUZU + sumMapSnd abs} (sym p) }=    
>               ( (snd ab) + sumMapSnd abs )
>             ={ Refl }=  
>               ( sumMapSnd (ab :: abs) )
>             QED  
>   | (No _)  = ( sumMapSnd (ab :: discardBySndZero abs) )
>             ={ Refl }=
>               ( (snd ab) + sumMapSnd (discardBySndZero abs) )
>             ={ cong (discardBySndZeroLemma abs) }=
>               ( (snd ab) + sumMapSnd abs )  
>             ={ Refl }=
>               ( sumMapSnd (ab :: abs) )
>             QED

> |||
> discardBySndZeroLemma1 : {A, B : Type} -> (Num B, DecEq B) => 
>                          (a : A) -> (b : B) -> Not (b = 0) ->
>                          discardBySndZero ((a, b) :: Nil) = (a, b) :: Nil
> discardBySndZeroLemma1 a b contra with (decEq b 0)
>   | (Yes prf) = void (contra prf)
>   | (No _)  = Refl
