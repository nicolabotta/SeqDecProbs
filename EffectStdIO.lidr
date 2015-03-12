> module EffectStdIO


> import Effects
> import Effect.StdIO
> import Effect.Exception

> import EffectException


> -- %default total


> |||
> getNat : { [STDIO] } Eff Nat
> getNat = 
>   do putStr (" Nat: " )
>      case the (Either String Nat) (run (parseNat (trim !getStr))) of
>           Left err => do putStr (err ++ "\n")
>                          getNat         
>           Right n  => do putStr "thanks!\n"
>                          pure n


> |||
> getBoundedNat : Nat -> { [STDIO] } Eff Nat
> getBoundedNat b = 
>   do putStr (" Nat, < " ++ cast (cast b) ++ ": " )
>      case the (Either String Nat) (run (parseBoundedNat b (trim !getStr))) of
>           Left err => do putStr (err ++ "\n")
>                          getBoundedNat b           
>           Right n  => do putStr "thanks!\n"
>                          pure n


-- Local Variables:
-- idris-packages: ("effects")
-- End:
