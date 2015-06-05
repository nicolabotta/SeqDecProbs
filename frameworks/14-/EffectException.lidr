> module EffectException


> import Effects
> import Effect.Exception

> import NatProperties
> import BoundedNat


> %default total


> ||| Parses a string for a Nat
> parseNat : String -> { [EXCEPTION String] } Eff Nat
> parseNat str
>   = if all (\x => isDigit x) (unpack str)
>     then pure (cast {to = Nat} (cast {to = Int} str))
>     else raise "Not a Nat!"


> ||| Parses a string for a bounded Nat
> parseLTB : (b : Nat) -> String -> { [EXCEPTION String] } Eff (LTB b)
> parseLTB b str
>   = if all (\x => isDigit x) (unpack str)
>     then let n = cast {to = Nat} (cast {to = Int} str) in
>          case (decLT n b) of
>            (Yes p) => pure (MkSigma n p)
>            (No _)  => raise "Out of bound!"
>     else raise "Not a Nat!"


> ||| Parses a string for an Int
> parseInt : String -> { [EXCEPTION String] } Eff Int
> parseInt str
>   = if all (\x => isDigit x || x == '-') (unpack str)
>     then pure (cast {to = Int} str)
>     else raise "Not an Int!"


-- Local Variables:
-- idris-packages: ("effects")
-- End:
