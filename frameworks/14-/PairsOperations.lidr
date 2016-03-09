> module PairsOperations


> import Sigma


> %default total

> %access public export
> %hide getWitness
> %hide getProof


> namespace Exists
>   getWitness : {P : a -> Type} -> Exists {a} P -> a
>   getWitness (Evidence x pf) = x
>   getProof : {P : a -> Type} -> (x : Exists {a} P) -> P (getWitness x)
>   getProof (Evidence x pf) = pf


> namespace Subset
>   getWitness : {P : a -> Type} -> Subset a P -> a
>   getWitness (Element x pf) = x
>   getProof : {P : a -> Type} -> (x : Subset a P) -> P (getWitness x)
>   getProof (Element x pf) = pf


> namespace Sigma
>   getWitness : {P : a -> Type} -> Sigma a P -> a
>   getWitness (MkSigma x pf) = x
>   getProof : {P : a -> Type} -> (x : Sigma a P) -> P (getWitness x)
>   getProof (MkSigma x pf) = pf


> {-

> ---}

