> module FunProperties

> import Syntax.PreorderReasoning

> import FunOperations
> import PairProperties


> %default total
> %access public export
> %auto_implicits on


> ||| Injectivity (one direction)
> Injective1 : {A, B : Type} -> (f : A -> B) -> Type
> Injective1 {A} f = (a1 : A) -> (a2 : A) -> f a1 = f a2 -> a1 = a2


> ||| Injectivity (the other direction)
> Injective2 : {A, B : Type} -> (f : A -> B) -> Type
> Injective2 {A} f = (a1 : A) -> (a2 : A) -> Not (a1 = a2) -> Not (f a1 = f a2)


> ||| Non injectivity, constructive
> NonInjective : {A, B : Type} -> (f : A -> B) -> Type
> NonInjective f = Exists (\ a1 => Exists (\ a2 => (Not (a1 = a2) , f a1 = f a2)))


> ||| Surjectivity
> Surjective : {A, B : Type} -> (f : A -> B) -> Type
> Surjective {B} f = (b : B) -> Exists (\ a => f a = b)


> ||| Non surjectivity, constructive
> NonSurjective : {A, B : Type} -> (f : A -> B) -> Type
> NonSurjective {A} f = Exists (\ b => (a : A) -> Not (f a = b))


Relationships of injectivity notions

> ||| Injective1 implies Injective2
> injectiveLemma : {A, B : Type} -> (f : A -> B) -> Injective1 f -> Injective2 f
> injectiveLemma f i1f a1 a2 contra = contra . (i1f a1 a2)
> %freeze injectiveLemma -- frozen


Properties of constructive proofs

> ||| NonInjective => Not Injective
> nonInjectiveNotInjective : {A, B : Type} -> (f : A -> B) -> NonInjective f -> Not (Injective1 f)
> nonInjectiveNotInjective f (Evidence a1 (Evidence a2 (na1eqa2 , fa1eqfa2))) =
>   \ injectivef => na1eqa2 (injectivef a1 a2 fa1eqfa2)
> %freeze nonInjectiveNotInjective -- frozen


> ||| NonSurjective => Not Surjective
> nonSurjectiveNotSurjective : {A, B : Type} -> (f : A -> B) -> NonSurjective f -> Not (Surjective f)
> nonSurjectiveNotSurjective f (Evidence b faanfab) =
>   \ surjectivef => let a = (getWitness (surjectivef b)) in (faanfab a) (getProof (surjectivef b))
> %freeze nonSurjectiveNotSurjective -- frozen


Properties of cross

> |||
> crossAnyIdFstLemma : fst ((cross f Prelude.Basics.id) (a,b)) = f a
> crossAnyIdFstLemma {a} {b} {f} = Refl


> |||
> crossAnyIdFstLemma' : fst ((cross f Prelude.Basics.id) ab) = f (fst ab)
> crossAnyIdFstLemma' {ab} {f} = 
>     ( fst ((cross f Prelude.Basics.id) ab) )
>   ={ cong {f = \ ZUZU => fst ((cross f Prelude.Basics.id) ZUZU)} (pairLemma ab) }=
>     ( fst ((cross f Prelude.Basics.id) (fst ab, snd ab)) )
>   ={ Refl }=
>     ( fst (f (fst ab), id (snd ab)) )
>   ={ Refl }=
>     ( f (fst ab) )
>   QED


> |||
> crossAnyIdSndLemma : snd ((cross f Prelude.Basics.id) (a,b)) = b
> crossAnyIdSndLemma {a} {b} {f} = Refl


> |||
> crossAnyIdSndLemma' : snd ((cross f Prelude.Basics.id) ab) = snd ab
> crossAnyIdSndLemma' {ab} {f} = 
>     ( snd ((cross f Prelude.Basics.id) ab) )
>   ={ cong {f = \ ZUZU => snd ((cross f Prelude.Basics.id) ZUZU)} (pairLemma ab) }=
>     ( snd ((cross f Prelude.Basics.id) (fst ab, snd ab)) )
>   ={ Refl }=
>     ( snd (f (fst ab), id (snd ab)) )
>   ={ Refl }=
>     ( snd (f (fst ab), snd ab) )
>   ={ Refl }=
>     ( snd ab )
>   QED


> |||
> crossIdAnyFstLemma : fst ((cross Prelude.Basics.id f) (a,b)) = a
> crossIdAnyFstLemma {a} {b} {f} = Refl


> {-

> ---}
