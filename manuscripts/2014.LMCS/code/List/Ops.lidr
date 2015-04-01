> module Ops


> rescale : Float -> List (alpha, Float) -> List (alpha, Float)

-- > rescale t axs = [(a, x * t) | (a, x) <- axs]

> rescale t axs = map (\ (a,x) => (a,x * t)) axs

rescale 1 = id

