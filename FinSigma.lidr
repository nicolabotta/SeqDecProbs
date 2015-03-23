> module FinSigma

> import Control.Isomorphism
> import IsomorphismOperations
> import Syntax.PreorderReasoning

> import Basics


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

> finSigma A A' B B' isoA isoBa isoBa' = MkIso toQ fromQ toFromQ fromToQ 
>   where toQ      : Sigma A  B  -> Sigma A' B'
>         toQ   (a ** b)   = (to isoA a ** to (isoBa a) b)
>         fromQ    : Sigma A' B' -> Sigma A  B
>         fromQ (a' ** b') = (from isoA a' ** from (isoBa' a') b')
>         toFromQ  : (ab' : Sigma A' B') -> toQ (fromQ ab') = ab'
>         toFromQ  (a' ** b') = 
>             ( toQ (fromQ (a' ** b'))                                                      )
>           ={ Refl }=
>             ( toQ (from isoA a' ** from (isoBa' a') b')                                   )
>           ={ Refl }=
>             ( (to isoA (from isoA a') ** to (isoBa (from isoA a')) (from (isoBa' a') b')) )
>           ={ sigmaEqLemma2 (toFrom isoA) (lemma1 A A' B B' isoA isoBa isoBa') }=
>             ( (a' ** b')                                                                  )
>           QED
>         fromToQ  : (ab  : Sigma A  B ) -> fromQ (toQ ab) = ab
>         fromToQ  (a ** b) = ?qq4

TODO: make toQ and fromQ only use one of isoBa and isoBa' (perhaps
create lemma to translate betwen).


