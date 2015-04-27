> import Data.Vect
> import Data.Fin
> %default total

> Dec1 : {A : Type} -> (P : A -> Type) -> Type
> Dec1 {A} P = (a : A) -> Dec (P a) 

> filterDec : {A : Type} -> {P : A -> Type} ->
>             Dec1 P -> Vect n A -> Sigma Nat (\m => Vect m A)
> filterDec dP Nil = (Z ** Nil)
> filterDec dP (a :: as) with (filterDec dP as)
>   | (n ** as') with (dP a)
>     | (Yes _) = (S n ** a :: as')
>     | (No  _) = (n ** as')

> Injective1 : Vect n t -> Type
> Injective1 {n} xs = (i : Fin n) -> (j : Fin n) -> index i xs = index j xs -> i = j

> replacePreservesValue1 : {a : _} -> {x : _} -> {y : _} -> {P : a -> Type} -> 
>                          (prf : x = y) -> (px : P x) -> replace prf px = px
> replacePreservesValue1 Refl px = Refl

> replacePreservesValue2 : {a : _} -> {x : _} -> {y : _} -> {P : a -> Type} -> 
>                          (prf : x = y) -> (px : P x) -> px = replace prf px
> replacePreservesValue2 Refl px = Refl

> replaceLemma1 : {a : _} -> {x : _} -> {y : _} -> {P : a -> Type} -> 
>                (prf : x = y) -> (px : P x) -> replace {P} (sym prf) (replace {P} prf px) = px
> replaceLemma1 Refl px = Refl

> replace2 : {a : _} -> {a1 : _} -> {a2 : _} -> 
>            {b : _} -> {b1 : _} -> {b2 : _} -> 
>            {P : a -> b -> Type} ->
>            (a1 = a2) -> (b1 = b2) -> P a1 b1 -> P a2 b2 
> replace2 Refl Refl p = p

> replace3 : {a : _} -> {a1 : _} -> {a2 : _} -> 
>            {b : _} -> {b1 : _} -> {b2 : _} -> 
>            {c : _} -> {c1 : _} -> {c2 : _} -> 
>            {P : a -> b -> c -> Type} ->
>            (a1 = a2) -> (b1 = b2) -> (c1 = c2) -> P a1 b1 c1 -> P a2 b2 c2
> replace3 Refl Refl Refl p = p

> adHoc : {n1 : Nat} -> {j1 : Fin n1} -> {k1 : Fin n1} ->
>         {n2 : Nat} -> {j2 : Fin n2} -> {k2 : Fin n2} ->
>         (xs1 : Vect n1 t) -> (xs2 : Vect n2 t) ->
>         n1 = n2 ->
>         j1 = j2 ->
>         k1 = k2 ->
>         xs1 = xs2 ->
>         index j1 xs1 = index k1 xs1 -> 
>         index j2 xs2 = index k2 xs2
> adHoc _ _ Refl Refl Refl Refl p = p

> depReplace4 : {A : Type} ->
>               {B : A -> Type} -> 
>               {C : (a : A) -> (b : B a) -> Type} ->
>               {D : (a : A) -> (b : B a) -> (c : C a b) -> Type} ->
>               {a1 : A} -> {b1 : B a1} -> {c1 : C a1 b1} -> {d1 : D a1 b1 c1} ->
>               {a2 : A} -> {b2 : B a2} -> {c2 : C a2 b2} -> {d2 : D a2 b2 c2} ->
>               {P : (a : A) -> (b : B a) -> (c : C a b) -> (d : D a b c) -> Type} ->
>               a1 = a2 ->
>               b1 = b2 ->
>               c1 = c2 ->
>               d1 = d2 ->
>               P a1 b1 c1 d1 -> 
>               P a2 b2 c2 d2
> depReplace4 Refl Refl Refl Refl p = p

> injectiveTailLemma1 : (xs : Vect (S n) t) -> Injective1 xs -> Injective1 (tail xs)

> injectiveFilterDecLemma : 
>   {A : Type} -> {P : A -> Type} -> {n : Nat} ->
>   (dP : Dec1 P) -> (as : Vect n A) ->
>   Injective1 as -> Injective1 (getProof (filterDec dP as))
> injectiveFilterDecLemma {A} {P} {n = Z}   dP  Nil      iNil i j p = ?kiko
> injectiveFilterDecLemma {A} {P} {n = S m} dP (a :: as) iaas i j p with (filterDec dP as) proof q
>     | (fn ** fas) with (dP a)
>       | (Yes _) = ?todo
>       | (No  _) = s9 where
>         i' : Fin (getWitness (filterDec dP as))
>         i' = replace {P = \rec => Fin (getWitness rec)} q i
>         j' : Fin (getWitness (filterDec dP as))
>         j' = replace {P = \rec => Fin (getWitness rec)} q j
>         q1 : fn = getWitness (filterDec dP as)
>         q1 = replace {P = \rec => fn = getWitness rec} q Refl
>         q2 : fas = getProof (filterDec dP as)
>         q2 = replace {P = \rec => fas = getProof rec} q Refl
>         s0 : i = i'
>         s0 = replacePreservesValue2 {P = \rec => Fin (getWitness rec)} q i
>         s3 : j = j'
>         s3 = replacePreservesValue2 {P = \rec => Fin (getWitness rec)} q j
>         p' : index i' (getProof (filterDec dP as)) = index j' (getProof (filterDec dP as))
>         p' = depReplace4 {A = Nat} 
>                          {B = \ a => Fin a} 
>                          {C = \a => \ b => Fin a} 
>                          {D = \ a => \b => \ c => Vect a A}
>                          {a1 = fn}                           {b1 = i}  {c1 = j}  {d1 = fas} 
>                          {a2 = getWitness (filterDec dP as)} {b2 = i'} {c2 = j'} {d2 = getProof (filterDec dP as)}
>                          {P = \ a => \ b => \ c => \ d => index b d = index c d} 
>                          q1 s0 s3 q2 p
>         {-         
>         p' = adHoc {n1 = fn} {j1 = i} {k1 = j}
>                    {n2 = getWitness (filterDec dP as)} {j2 = i'} {k2 = j'}
>                    fas (getProof (filterDec dP as)) q1 s0 s3 q2 p
>         -}
>         s4 : i' = j'
>         s4 = injectiveFilterDecLemma dP as (injectiveTailLemma1 (a :: as) iaas) i' j' p'
>         i'' : Fin fn
>         i'' = replace {P = \rec => Fin (getWitness rec)} (sym q) i'
>         j'' : Fin fn
>         j'' = replace {P = \rec => Fin (getWitness rec)} (sym q) j'
>         s5  : i'' = j''
>         s5  = cong s4
>         s7  : i'' = i
>         s7  = replaceLemma1 {P = \rec => Fin (getWitness rec)} q i
>         s8  : j'' = j
>         s8  = replaceLemma1 {P = \rec => Fin (getWitness rec)} q j
>         s9  : i = j
>         s9  = replace2 {P = \ a => \ b => a = b} s7 s8 s5


