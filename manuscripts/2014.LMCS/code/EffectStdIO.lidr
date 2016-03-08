> module EffectStdIO

> import Effects
> import Effect.StdIO
> import Effect.Exception
> import Data.So

> import EffectException
> import BoundedNat.Blt


> %default total

> %access public export


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
> getBlt : (b : Nat) -> { [STDIO] } Eff (Blt b)
> getBlt b =
>   do putStr (" Nat, < " ++ cast {from = Int} (cast b) ++ ": " )
>      case the (Either String (Blt b)) (run (parseBlt b (trim !getStr))) of
>           Left err => do putStr (err ++ "\n")
>                          getBlt b
>           Right n  => do putStr "thanks!\n"
>                          pure n


-- Local Variables:
-- idris-packages: ("effects")
-- End:
