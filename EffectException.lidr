> module EffectException
 

> import Effects
> import Effect.Exception


> -- %default total


> ||| 
> parseNat : String -> { [EXCEPTION String] } Eff Nat
> parseNat str
>   = if all (\x => isDigit x) (unpack str)
>     then pure (cast (cast str))
>     else raise "Not a Nat!"


> ||| 
> parseBoundedNat : Nat -> String -> { [EXCEPTION String] } Eff Nat
> parseBoundedNat b str
>   = if all (\x => isDigit x) (unpack str)
>     then let n = cast str in
>          if (n < (cast b))
>          then pure (cast n)
>          else raise "Out of bound!"
>     else raise "Not a Nat!"



-- Local Variables:
-- idris-packages: ("effects")
-- End:
