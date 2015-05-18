module Main

import Effect.StdIO
import Effect.State

test : Handler StdIO e => Eff e [STDIO, STATE String] ()
test = do putStr "Name? "
          n <- getStr
          put n
          putStrLn ("Hello " ++ show n)

main : IO ()
main = run [(), ""] test

