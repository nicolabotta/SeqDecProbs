> module Properties

> import Data.So

> import Rel.Syntax
> import Double.Postulates

> %default total

> %access public export


> reflexive_Double_lte : reflexive Double (<=)
> reflexive_Double_lte x = sub_Double_eqeq_lte (reflexive_Double_eqeq x)
