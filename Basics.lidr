> module Basics


> %default total


Replace extensions:

> replace2 : {a : _} -> {a1 : _} -> {a2 : _} -> 
>            {b : _} -> {b1 : _} -> {b2 : _} -> 
>            {P : a -> b -> Type} ->
>            (a1 = a2) -> (b1 = b2) -> P a1 b1 -> P a2 b2 
> replace2 Refl Refl p = p


Replace properties:


> |||
> replaceLemma : {a : _} -> {x : _} -> {y : _} -> {P : a -> Type} -> 
>                (prf : x = y) -> (px : P x) -> replace prf px = px
> replaceLemma Refl px = Refl


> |||
> replaceLemma2 : {A : Type} -> {P : A -> Type} -> {Q : (a : A) -> P a -> Type} -> 
>                 {a1 : A} -> {a2 : A} ->
>                 (f : (a : A) -> (pa : P a) -> Q a pa) ->
>                 (prf : a1 = a2) -> 
>                 (pa2 : P a2) -> 
>                 f a1 (replace (sym prf) pa2) = f a2 pa2
> replaceLemma2 f Refl pa2 = Refl


Cong extensions:

> cong1 : {alpha : Type} ->
>         {beta : Type} ->
>         {a1 : alpha} ->
>         {a2 : alpha} ->
>         (f : alpha -> beta) -> 
>         (a1 = a2) -> 
>         f a1 = f a2
> cong1 f Refl = Refl

> cong2 : {alpha : Type} ->
>         {beta : Type} ->
>         {gamma : Type} ->
>         {a1 : alpha} ->
>         {a2 : alpha} ->
>         {b1 : beta} ->
>         {b2 : beta} ->
>         (f : alpha -> beta -> gamma) -> 
>         (a1 = a2) -> 
>         (b1 = b2) -> 
>         f a1 b1 = f a2 b2
> cong2 f Refl Refl = Refl


> depCong1 : {alpha : Type} -> 
>            {P : alpha -> Type} ->
>            {a1 : alpha} ->
>            {a2 : alpha} ->
>            (f : (a : alpha) -> P a) -> 
>            (a1 = a2) -> 
>            f a1 = f a2
> depCong1 f Refl = Refl

> depCong2 : {alpha : Type} -> 
>            {P : alpha -> Type} ->
>            {gamma : Type} ->
>            {a1 : alpha} -> 
>            {a2 : alpha} ->
>            {Pa1 : P a1} ->
>            {Pa2 : P a2} -> 
>            (f : (a : alpha) -> P a -> gamma) -> 
>            (a1 = a2) ->
>            (Pa1 = Pa2) -> 
>            f a1 Pa1 = f a2 Pa2
> depCong2 f Refl Refl = Refl

> depCong2' : {alpha : Type} -> 
>             {P : alpha -> Type} ->
>             {Q : (a : alpha) -> P a -> Type} ->
>             {a1 : alpha} -> 
>             {a2 : alpha} ->
>             {Pa1 : P a1} ->
>             {Pa2 : P a2} -> 
>             (f : (a : alpha) -> (pa : P a) -> Q a pa) -> 
>             (a1 = a2) ->
>             (Pa1 = Pa2) -> 
>             f a1 Pa1 = f a2 Pa2
> depCong2' f Refl Refl = Refl

