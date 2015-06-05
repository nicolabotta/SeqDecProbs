> module Postulates

> import Data.So

> import Rel.Syntax


> postulate sub_Float_eqeq_lte : sub Float (==) (<=)

> postulate sub_Float_lt_lte : sub Float (<) (<=)

> postulate reflexive_Float_eqeq : reflexive Float (==)

> postulate symmetric_Float_eqeq : symmetric Float (==)

> postulate transitive_Float_lte : transitive Float (<=)

> postulate monotone_Float_plus_lte : monotone Float (+) (<=)

> postulate monotone'_Float_plus_lte : monotone' Float (+) (<=)





