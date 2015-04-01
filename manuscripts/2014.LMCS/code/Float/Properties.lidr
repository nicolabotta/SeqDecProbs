> module Properties

> import Rel.Syntax
> import Float.Postulates

> %default total

> reflexive_Float_lte : reflexive Float (<=)
> reflexive_Float_lte x = sub_Float_eqeq_lte (reflexive_Float_eqeq x)


