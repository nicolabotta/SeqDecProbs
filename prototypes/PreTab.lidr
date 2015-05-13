A sketch for one way of getting rid of exponential blow-up in the
cardinality of RVX.

This may take us most of the way (after adding indices to X etc.)

Then we can explore erasure to get rid of proofs at runtime.

> module PreTab
> import Data.Fin
> import Data.Vect
> import Prop
> import Finite
> import FiniteOperations
> import FiniteProperties
> import VectOperations
> import VectProperties
> import Decidable
> postulate X : Type
> postulate fX : Finite X
> postulate RV : X -> Prop
> postulate decRV : Dec1 RV
> n : Nat
> n = getWitness fX
> rX : Vect n X
> rX = toVect fX
> mfrX : (m : Nat ** Vect m X)
> mfrX = filter decRV rX
> m : Nat
> m = getWitness mfrX
> frX : Vect m X
> frX = getProof mfrX
> postulate x : X
> postulate rv : RV x
> p : Elem x rX
> p = toVectComplete fX x
> k : Fin m
> k = lookup x frX (filterLemma decRV x rX p rv)
