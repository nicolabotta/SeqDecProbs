> module Main

> import Effects
> import Effect.Exception
> import Effect.StdIO

> import EffectException
> import EffectStdIO

> %default total


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
