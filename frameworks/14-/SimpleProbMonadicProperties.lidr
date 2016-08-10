> module SimpleProbMonadicProperties

> import Data.List
> import Data.List.Quantifiers
> import Syntax.PreorderReasoning

> import SimpleProb
> import SimpleProbBasicOperations
> import SimpleProbBasicProperties
> import SimpleProbMonadicOperations
> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties

> import NatPositive
> import FractionNormal
> import NumRefinements
> import NumProperties
> import FunOperations
> import ListOperations
> import ListProperties
> import Unique
> import Finite
> import Sigma

> import NatCoprime

> %default total
> -- %access public export
> %access export
> %auto_implicits off


* Properties of |normalize|, |support| and |ret|:

> |||
> normalizeRetLemma : {A : Type} -> (a : A) -> normalize (ret a) = ret a
> normalizeRetLemma a = ( normalize (ret a) )
>                     ={ Refl }=
>                       ( normalize (MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1)) )
>                     ={ Refl }=
>                       ( MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1) ) 
>                     ={ Refl }=  
>                       ( ret a )
>                     QED
> {-
> normalizeRetLemma a = s9 where
>   s1 : normalize (ret a) = normalize (MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1))
>   s1 = Refl
>   s2 : normalize (MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1))
>        =
>        MkSimpleProb (discardBySndZero ((a, 1) :: Nil)) 
>                     (trans (discardBySndZeroLemma ((a, 1) :: Nil)) (sumMapSndSingletonLemma a 1))
>   s2 = Refl                  
>   s3 : discardBySndZero ((a, 1) :: Nil) = (a, 1) :: Nil
>   s3 = discardBySndZeroLemma1 a 1 ?oneNotZero
>   s4 : discardBySndZeroLemma ((a, 1) :: Nil) = Refl {} {} {}
>   s4 = ?lika
>   s5 : MkSimpleProb (discardBySndZero ((a, 1) :: Nil)) 
>                     (trans (discardBySndZeroLemma ((a, 1) :: Nil)) (sumMapSndSingletonLemma a 1))
>        =
>        MkSimpleProb ((a, 1) :: Nil) (trans Refl (sumMapSndSingletonLemma a 1))
>   s5 = ?leka
>   s6 : MkSimpleProb ((a, 1) :: Nil) (trans Refl (sumMapSndSingletonLemma a 1))
>        = 
>        MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1)
>   s6 = Refl
>   s7 : MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1) = ret a
>   s7 = Refl
>   s9 : normalize (ret a) = ret a
>   s9 = trans s1 (trans s2 (trans s5 (trans s6 s7)))
> -}

> |||
> supportRetLemma : {A : Type} -> 
>                   (a : A) -> support (SimpleProbMonadicOperations.ret a) = ListOperations.ret a
> supportRetLemma a = ( support (SimpleProbMonadicOperations.ret a) )
>                   ={ Refl }=
>                     ( map fst (toList (normalize (SimpleProbMonadicOperations.ret a))) )
>                   ={ cong {f = \ X => map Prelude.Basics.fst (toList X)} (normalizeRetLemma a) }=
>                     ( map fst (toList (SimpleProbMonadicOperations.ret a)) )
>                   ={ Refl }=
>                     ( map fst (toList (MkSimpleProb ((a, 1) :: Nil) (sumMapSndSingletonLemma a 1))) )
>                   ={ Refl }=
>                     ( map fst ((a, 1) :: Nil) )  
>                   ={ Refl }=
>                     ( a :: Nil )  
>                   ={ Refl }=
>                     ( ListOperations.ret a )
>                   QED 


* |SimpleProb| is a container monad:

> |||
> elemNonEmptySpec0 : {A : Type} ->
>                     (a : A) -> (sp : SimpleProb A) ->
>                     a `Elem` sp -> SimpleProbMonadicOperations.NonEmpty sp
> elemNonEmptySpec0 {A} a sp aesp = ListProperties.elemNonEmptySpec0 a (support sp) aesp

> |||
> elemNonEmptySpec1 : {A : Type} ->
>                     (sp : SimpleProb A) ->
>                     SimpleProbMonadicOperations.NonEmpty sp -> Sigma A (\ a => a `Elem` sp)
> elemNonEmptySpec1 {A} sp nesp = ListProperties.elemNonEmptySpec1 (support sp) nesp

> |||
> containerMonadSpec1 : {A : Type} -> {a : A} -> a `SimpleProbMonadicOperations.Elem` (ret a)
> containerMonadSpec1 {A} {a} = s3 where
>   s1 : a `Data.List.Elem` (ListOperations.ret a)
>   s1 = ListProperties.containerMonadSpec1
>   s2 : a `Data.List.Elem` (support (SimpleProbMonadicOperations.ret a))
>   s2 = replace {P = \ X => a `Data.List.Elem` X} (sym (supportRetLemma a)) s1
>   s3 : a `SimpleProbMonadicOperations.Elem` (ret a)
>   s3 = s2

> |||
> containerMonadSpec3 : {A : Type} -> {P : A -> Type} ->
>                       (a : A) -> (sp : SimpleProb A) ->
>                       All P sp -> a `Elem` sp -> P a
> containerMonadSpec3 {A} {P} a sp allp elemp = ListProperties.containerMonadSpec3 a (support sp) allp elemp



* Specific container monad properties

> |||
> uniqueAllLemma : {A : Type} -> {P : A -> Type} -> 
>                  Unique1 P -> (sp : SimpleProb A) -> Unique (All P sp)
> uniqueAllLemma u1P sp = ListProperties.uniqueAllLemma u1P (support sp)

> |||
> finiteAll : {A : Type} -> {P : A -> Type} -> 
>             Finite1 P -> (sp : SimpleProb A) -> Finite (All P sp)
> finiteAll f1P sp = ListProperties.finiteAll f1P (support sp)

> ||| NotEmpty is finite
> finiteNonEmpty : {A : Type} -> (sp : SimpleProb A) -> Finite (SimpleProbMonadicOperations.NonEmpty sp)
> finiteNonEmpty sp = ListProperties.finiteNonEmpty (support sp)


* |SimpleProb|s are never empty

> |||
> nonEmptyLemma1 : {A : Type} -> (sp : SimpleProb A) -> ListOperations.NonEmpty (toList sp)
> nonEmptyLemma1 {A} (MkSimpleProb Nil s1p) = void s9 where
>   s1 : sumMapSnd {A = A} {B = NonNegRational} Nil = 0
>   s1 = sumMapSndNilLemma {A = A} {B = NonNegRational}
>   s2 : sumMapSnd {A = A} {B = NonNegRational} Nil = 1
>   s2 = s1p
>   s3 : (=) {A = NonNegRational} {B = NonNegRational} 1 0
>   s3 = trans (sym s2) s1
>   s9 : Void
>   s9 = not1Eq0 s3
> nonEmptyLemma1 (MkSimpleProb (ap :: aps) s1p) = () 

> |||
> nonEmptyLemma : {A : Type} -> (sp : SimpleProb A) -> NonEmpty sp
> nonEmptyLemma {A} sp = s4 where
>   s1 : ListOperations.NonEmpty (toList (normalize sp))
>   s1 = nonEmptyLemma1 (normalize sp)
>   s2 : ListOperations.NonEmpty (map fst (toList (normalize sp)))
>   s2 = mapPreservesNonEmpty fst (toList (normalize sp)) s1
>   s3 : ListOperations.NonEmpty (support sp) 
>   s3 = s2
>   s4 : NonEmpty sp
>   s4 = s3



> {-

> ---}
