> module Properties


> import Rel.Syntax
> import Rel.Postulates

> eqTrans : {A : Set} -> {a1 : A} -> {a2 : A} -> {a3 : A} ->
>           a1 = a2 -> a2 = a3 -> a1 = a3
> eqTrans {a1} {a2} {a3} p12 p23 = replace -- {P = \ a => a1 = a}
>                                          p23 p12




