> import Data.Fin
> import Control.Isomorphism

> %default total

> postulate lambdaLemma1 : {A, B : Type} -> (f : A -> B) -> (\ a => f a) = f

> isoCong : {A : Type} -> {x : A} -> {y : A} -> {P : A -> Type} -> x = y -> Iso (P x) (P y)
> isoCong {x} {P} prf = replace {P = \ z => Iso (P x) (P z)} prf isoRefl 

> tail : {A : Type} -> (Fin (S n) -> A) -> (Fin n -> A)
> tail f k = f (FS k)

> sigmaFinEitherLemma : {n : Nat} -> 
>                       {P : Fin (S n) -> Type} ->
>                       Iso (Sigma (Fin (S n)) P) (Either (P FZ) (Sigma (Fin n) (tail P)))

> sigmaFinEitherLemma1 : {n : Nat} -> {f : Fin (S n) -> Nat} ->
>                        Iso 
>                        (Sigma (Fin (S n)) (\ k => Fin (f k))) 
>                        (Either (Fin (f FZ)) (Sigma (Fin n) (\ k => Fin ((tail f) k))))
> {-                       
> sigmaFinEitherLemma1 {n} {f} =
>     ( Sigma (Fin (S n)) (\ k => Fin (f k))                            ) 
>   ={ isoCong {P = \ X => (Sigma (Fin (S n)) X)} (lambdaLemma1 (Fin . f)) }=
>     ( Sigma (Fin (S n)) (Fin . f)                            ) 
>   ={ sigmaFinEitherLemma {n = n} {P = Fin . f} }=
>     ( Either (Fin (f FZ)) (Sigma (Fin n) (tail (Fin . f)))            )     
>   ={ isoRefl }=
>     ( Either (Fin (f FZ)) (Sigma (Fin n) (\ k => (tail (Fin . f)) k)) )     
>   ={ isoRefl }=
>     ( Either (Fin (f FZ)) (Sigma (Fin n) (\ k => Fin ((tail f) k)))   )
>   QED
> -}
> sigmaFinEitherLemma1 {n} {f} =
>     ( Sigma (Fin (S n)) (\ k => Fin (f k))                            ) 
>   ={ isoCong {P = \ X => (Sigma (Fin (S n)) X)} (lambdaLemma1 (Fin . f)) }=
>     ( Sigma (Fin (S n)) (Fin . f)                            ) 
>   ={ sigmaFinEitherLemma {n = n} {P = Fin . f} }=
>     ( Either (Fin (f FZ)) (Sigma (Fin n) (tail (Fin . f)))            )     
>   ={ isoCong {P = \ X => Either (Fin (f FZ)) (Sigma (Fin n) X)} (sym (lambdaLemma1 (tail (Fin . f)))) }=
>     ( Either (Fin (f FZ)) (Sigma (Fin n) (\ k => (tail (Fin . f)) k)) )     
>   ={ isoRefl }=
>     ( Either (Fin (f FZ)) (Sigma (Fin n) (\ k => Fin ((tail f) k)))   )
>   QED
