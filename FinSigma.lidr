> module SigmaProperties

> import Control.Isomorphism
> import IsomorphismOperations

> %default total


Finitess properties

finSigma :  {A : Type} -> {A' : Type} ->  {B : A -> Type} -> {B' : A' -> Type} -> 

> finSigma :  (A : Type) -> (A' : Type) ->  (B : A -> Type) -> (B' : A' -> Type) -> 
>             (isoA : Iso A A') -> 
>             (isoBa  : (a : A) -> Iso (B a)               (B' (to isoA a)) ) ->
>             (isoBa' : (a': A')-> Iso (B (from isoA a'))  (B' a')          ) ->
> --          (isoBaa': (a : A) -> (a' : A') -> (a = a') -> Iso (B a) (B' a')) -> -- not correct
>             Iso (Sigma A B) (Sigma A' B')

Only one of isoBa, isoBa' and a corrected version of isoBaa' should be
enough, but starting out I'm not sure which is more convenient in the
proof.

> finSigma A A' B B' (MkIso to from toFrom fromTo) isoBa isoBa' = 
>                          MkIso toQ fromQ toFromQ fromToQ where
>         toQ      : Sigma A  B  -> Sigma A' B'
>         toQ   (a ** b)   = (to a ** IsomorphismOperations.to (isoBa a) b)
>         fromQ    : Sigma A' B' -> Sigma A  B
>         fromQ (a' ** b') = (from a' ** IsomorphismOperations.from (isoBa' a') b')
>         toFromQ  : (ab' : Sigma A' B') -> toQ (fromQ ab') = ab'
>         toFromQ  (a' ** b') = ?qq3
>         fromToQ  : (ab  : Sigma A  B ) -> fromQ (toQ ab) = ab
>         fromToQ  (a ** b) = ?qq4

TODO: make toQ and fromQ only use one of isoBa and isoBa' (perhaps
create lemma to translate betwen).

