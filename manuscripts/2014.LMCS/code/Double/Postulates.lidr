> module Postulates

> import Data.So

> import Rel.Syntax

> %default total

> %access public export


> postulate sub_Double_eqeq_lte : sub Double (==) (<=)

> postulate sub_Double_lt_lte : sub Double (<) (<=)

> postulate reflexive_Double_eqeq : reflexive Double (==)

> postulate symmetric_Double_eqeq : symmetric Double (==)

> postulate transitive_Double_lte : transitive Double (<=)

> postulate monotone_Double_plus_lte : monotone Double (+) (<=)

> postulate monotone'_Double_plus_lte : monotone' Double (+) (<=)
