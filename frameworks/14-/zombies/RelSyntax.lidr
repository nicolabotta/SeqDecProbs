> module RelSyntax


> %default total


> syntax reflexive [alpha] [r] = 
>   (a : alpha) -> So (r a a)


> syntax transitive [alpha] [r] = 
>   {a1 : alpha} -> {a2 : alpha} -> {a3 : alpha} ->
>   So (r a1 a2) -> So (r a2 a3) -> So (r a1 a3)


> syntax monotone [alpha] [r] [op2] = 
>   {a1 : alpha} -> {a2 : alpha} ->
>   (a3 : alpha) -> So (r a1 a2) -> So (r (op2 a3 a1) (op2 a3 a2))
