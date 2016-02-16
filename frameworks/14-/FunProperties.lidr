> module FunProperties

> %default total

> %access public export


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


Properties of constructive proofs

> ||| NonInjective => Not Injective
> nonInjectiveNotInjective : {A, B : Type} -> (f : A -> B) -> NonInjective f -> Not (Injective1 f)
> nonInjectiveNotInjective f (Evidence a1 (Evidence a2 (na1eqa2 , fa1eqfa2))) =
>   \ injectivef => na1eqa2 (injectivef a1 a2 fa1eqfa2)


> ||| NonSurjective => Not Surjective
> nonSurjectiveNotSurjective : {A, B : Type} -> (f : A -> B) -> NonSurjective f -> Not (Surjective f)
> nonSurjectiveNotSurjective f (Evidence b faanfab) =
>   \ surjectivef => let a = (getWitness (surjectivef b)) in (faanfab a) (getProof (surjectivef b))
