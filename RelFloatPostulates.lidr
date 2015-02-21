> module RelFloatPostulates


> import Data.So

> import RelSyntax


> %default total 


> postulate reflexiveFloatLTE : reflexive Float (<=)


> postulate transitiveFloatLTE : transitive Float (<=)


> postulate monotoneFloatPlusLTE : monotone Float (<=) (+) 
