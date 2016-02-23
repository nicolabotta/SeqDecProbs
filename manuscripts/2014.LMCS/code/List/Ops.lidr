> module Ops


> rescale : Double -> List (alpha, Double) -> List (alpha, Double)

-- > rescale t axs = [(a, x * t) | (a, x) <- axs]

> rescale t axs = map (\ (a,x) => (a,x * t)) axs

rescale 1 = id
