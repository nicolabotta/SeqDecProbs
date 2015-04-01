> module TestIsIn

# A functor |M|

> M : Type -> Type

> Mmap : (alpha -> beta) -> M alpha -> M beta

> Mret : alpha -> M alpha

> Mbind : M alpha -> (alpha -> M beta) -> M beta

> Mjoin : M (M alpha) -> M alpha

> MisIn : alpha -> M alpha -> Bool

> MareAllTrue      :  M Bool -> Bool

> Many : (alpha -> Bool) -> M alpha -> Bool

> Mspec1 : (b : Bool) -> so (MareAllTrue (Mret b) == b)

> Mspec2 : (mx : M alpha) -> (p : alpha -> Bool) ->
>          so (MareAllTrue (Mmap p mx)) ->
>          (x : alpha) -> so (x `MisIn` mx) -> so (p x)

> Ax1 : (x : alpha) -> so (x `MisIn` (Mret x))

> Ax2 : (x : alpha) -> (mmx : M (M alpha)) -> so (Many (MisIn x) mmx) -> so (MisIn x (Mjoin mmx))

> MmapIn : (ma : M alpha) -> (f : (a : alpha) -> so (MisIn a ma) -> beta) -> M beta

> MmapInSpec : (ma : M alpha) -> (f : (a : alpha) -> so (MisIn a ma) -> beta) ->
>              MmapIn ma f = Mmap (\ a => f a (believe_me oh)) ma


