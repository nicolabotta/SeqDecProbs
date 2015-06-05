> module Syntax

> import Data.So


> %default total


> syntax reflexive [alpha] [r] = (a : alpha) -> So (r a a)

> syntax symmetric [alpha] [r] = {a1 : alpha} -> 
>                                {a2 : alpha} -> 
>                                So (r a1 a2) -> 
>                                So (r a2 a1)

> syntax transitive [alpha] [r] = {a1 : alpha} -> 
>                                 {a2 : alpha} -> 
>                                 {a3 : alpha} ->
>                                 So (r a1 a2) -> 
>                                 So (r a2 a3) ->
>                                 So (r a1 a3)

> syntax sub [alpha] [r1] [r2] = {a1 : alpha} ->
>                                {a2 : alpha} ->
>                                So (r1 a1 a2) ->
>                                So (r2 a1 a2)

> syntax monotone [alpha] [op2] [r] = {a1 : alpha} ->
>                                     {a2 : alpha} ->
>                                     (a3 : alpha) ->
>                                     So (r a1 a2) ->
>                                     So (r (op2 a3 a1) (op2 a3 a2))

> syntax monotone' [alpha] [op2] [r] = {a1 : alpha} ->
>                                      {a2 : alpha} ->
>                                      (a3 : alpha) ->
>                                      So (r (op2 a3 a1) (op2 a3 a2)) ->
>                                      So (r a1 a2)
