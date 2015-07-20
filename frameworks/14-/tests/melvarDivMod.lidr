> module Main

> import Effects
> import Effect.Exception
> import Effect.StdIO

> import Data.Nat.DivMod

> import EffectException
> import EffectStdIO

> %default total


> divmodNatNZ : (m : Nat) -> (n : Nat) -> Not (n = Z) -> (Nat, Nat)
> divmodNatNZ m  Z    p = void (p Refl)
> divmodNatNZ m (S n) p with (divMod m n)
>   | MkDivMod k r rLTm = (k, r)

> divNatNZ : (m : Nat) -> (n : Nat) -> Not (n = Z) -> Nat
> divNatNZ m n nnZ = fst (divmodNatNZ m n nnZ)

> modNatNZ : (m : Nat) -> (n : Nat) -> Not (n = Z) -> Nat
> modNatNZ m n nnZ = snd (divmodNatNZ m n nnZ)

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter m:\n")
>      m <- getNat
>      putStr ("enter n:\n")
>      n <- getNat
>      case (decEq n Z) of
>        (No contra) => do k <- pure (divNatNZ m n contra)
>                          putStr ("divNatNZ = " ++ show k ++ "\n")
>        (Yes p)     => putStr ("Error: n = Z\n")
> %freeze computation

> main : IO ()
> main = run computation
> %freeze main

> ---}

-- Local Variables:
-- idris-packages: ("effects")
-- End:
