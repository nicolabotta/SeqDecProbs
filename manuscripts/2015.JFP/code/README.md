TODOs:
* Generalise the reward from Double to some preorder
* Package all the assumptions (global metavariables) as a record (or a type class)
  * X, finX, decEqX,   -- State space
  * Y, finY,           -- Control space
  * step,              -- (monadic) step function
  * reward,
  * max, argmax, maxSpec, argmaxSpec,
  * MeasLib.measMon, MeasLib.meas,
  * MonadLib.M, MonadLib.fmap, MonadLib.bind,MonadLib.ret,
  * ContainerMonadLib.Elem, ContainerMonadLib.tagElem,
  * decAll, decElem
