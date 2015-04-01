> module Syntax


> syntax reflexive [alpha] [r] = (a : alpha) -> so (r a a)

> syntax symmetric [alpha] [r] = {a1 : alpha} -> 
>                                {a2 : alpha} -> 
>                                so (r a1 a2) -> 
>                                so (r a2 a1)

> syntax transitive [alpha] [r] = {a1 : alpha} -> 
>                                 {a2 : alpha} -> 
>                                 {a3 : alpha} ->
>                                 so (r a1 a2) -> 
>                                 so (r a2 a3) ->
>                                 so (r a1 a3)

> syntax sub [alpha] [r1] [r2] = {a1 : alpha} ->
>                                {a2 : alpha} ->
>                                so (r1 a1 a2) ->
>                                so (r2 a1 a2)

> syntax monotone [alpha] [op2] [r] = {a1 : alpha} ->
>                                     {a2 : alpha} ->
>                                     (a3 : alpha) ->
>                                     so (r a1 a2) ->
>                                     so (r (op2 a3 a1) (op2 a3 a2))

> syntax monotone' [alpha] [op2] [r] = {a1 : alpha} ->
>                                      {a2 : alpha} ->
>                                      (a3 : alpha) ->
>                                      so (r (op2 a3 a1) (op2 a3 a2)) ->
>                                      so (r a1 a2)
