> module Main

> import Effects
> import Effect.Exception
> import Effect.StdIO

> import EffectException
> import EffectStdIO

> %default total


> decLTE : (m : Nat) -> (n : Nat) -> Dec (LTE m n)
> decLTE Z _     = Yes LTEZero
> decLTE (S m) Z = No succNotLTEzero 
> decLTE (S m) (S n) with (decLTE m n)
>   | (Yes p) = Yes (LTESucc p)
>   | (No contra) = No (\ p => contra (fromLteSucc p))

> {-
> divmod : Nat -> Nat -> Nat -> (Nat, Nat)
> divmod  Z       centre right = (Z, centre)
> divmod (S left) centre right with (decLTE centre right)
>   | Yes _ = (Z, centre)
>   | No  _ = (S (fst dm), (snd dm)) where
>       dm : (Nat, Nat)
>       dm = divmod left (centre - S right) right 
> ---}

> --{-
> divmod : Nat -> Nat -> Nat -> (Nat, Nat)
> divmod  Z       centre right = (Z, centre)
> divmod (S left) centre right with (decLTE centre right)
>   | Yes _ = (Z, centre)
>   | No  _ = let dm = divmod left (centre - S right) right in (S (fst dm), (snd dm))
> ---}

> divmodNatNZ : (m : Nat) -> (n : Nat) -> Not (n = Z) -> (Nat, Nat)
> divmodNatNZ m  Z    p = void (p Refl)
> divmodNatNZ m (S n) p = divmod m m n 

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
>        (No contra) => do k <- pure (Main.divNatNZ m n contra)
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
