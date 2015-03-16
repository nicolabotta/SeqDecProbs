> module EffectStdIO


> import Effects
> import Effect.StdIO
> import Effect.Exception

> import EffectException
> import BoundedNat


> %default total


> |||
> %assert_total -- termination not required
> getNat : { [STDIO] } Eff Nat
> getNat = 
>   do putStr (" Nat: " )
>      case the (Either String Nat) (run (parseNat (trim !getStr))) of
>           Left err => do putStr (err ++ "\n")
>                          getNat         
>           Right n  => do putStr "thanks!\n"
>                          pure n


> |||
> %assert_total -- termination not required
> getLTB : (b : Nat) -> { [STDIO] } Eff (LTB b)
> getLTB b = 
>   do putStr (" Nat, < " ++ cast (cast b) ++ ": " )
>      case the (Either String (LTB b)) (run (parseLTB b (trim !getStr))) of
>           Left err => do putStr (err ++ "\n")
>                          getLTB b           
>           Right n  => do putStr "thanks!\n"
>                          pure n


-- Local Variables:
-- idris-packages: ("effects")
-- End:
