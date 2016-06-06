IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects --warnreach -V
IDRIS_CHECK_FLAGS = -p contrib -V --check
IDRIS_COMPILE_FLAGS = -p contrib -p effects -V

all:
	find . -not \( -path "./zombies" -prune \) -not \( -path "./unused" -prune \) -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} --check

libs: Basics.lidr \
			FunOperations.lidr \
			FunProperties.lidr \
			IsomorphismOperations.lidr \
			IsomorphismProperties.lidr \
			FinOperations.lidr \
			Sigma.lidr \
			PairsOperations.lidr \
			NatLTEProperties.lidr \
			NatBasicProperties.lidr \
			NatLTProperties.lidr \
			FinProperties.lidr \
			Preorder.lidr \
			TotalPreorder.lidr \
			TotalPreorderOperations.lidr \
			Decidable.lidr \
			VectOperations.lidr \
			ExistsOperations.lidr \
			Finite.lidr \
			FiniteOperations.lidr \
			SigmaOperations.lidr \
			VectProperties.lidr \
			FiniteProperties.lidr \
			SubsetOperations.lidr \
			Unique.lidr \
			SubsetProperties.lidr \
			NatPositive.lidr \
			UnitProperties.lidr \
			VoidProperties.lidr \
			ListOperations.lidr \
			ListProperties.lidr \
			PNat.lidr \
			NatPredicates.lidr \
			NatOperations.lidr \
			NatOperations.lidr \
			NatOperationsProperties.lidr \
			NatDivisor.lidr \
			NatDivisorOperations.lidr \
			NatDivisorProperties.lidr \
			NatGCD.lidr \
			NatGCDEuclid.lidr \
			EqualityProperties.lidr \
			NatGCDOperations.lidr \
			NatGCDProperties.lidr \
			NatGCDAlgorithm.lidr \
			NatCoprime.lidr \
			PNatOperations.lidr \
			Fraction.lidr \
			FractionBasicOperations.lidr \
			FractionNormal.lidr \
			NumRefinements.lidr \
			PNatProperties.lidr \
			NatCoprimeProperties.lidr \
			FractionBasicProperties.lidr \
			FractionPredicates.lidr \
			FractionLTEProperties.lidr \
			FractionEqProperties.lidr \
			FractionNormalize.lidr \
			FractionNormalizeProperties.lidr \
			NonNegRational.lidr \
			NonNegRationalBasicOperations.lidr \
			NonNegRationalPredicates.lidr \
			UniqueProperties.lidr \
			NonNegRationalBasicProperties.lidr \
			NonNegRationalLTEProperties.lidr \
			NonNegRationalMeasures.lidr \
			NonNegRationalMeasureProperties.lidr 
	${IDRIS} ${IDRIS_CHECK_FLAGS} Basics.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FunOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FunProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} IsomorphismOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} IsomorphismProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FinOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} Sigma.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} PairsOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatLTEProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatBasicProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatLTProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FinProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} Preorder.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} TotalPreorder.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} TotalPreorderOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} Decidable.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} VectOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} ExistsOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} Finite.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FiniteOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} SigmaOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} VectProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FiniteProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} SubsetOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} Unique.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} SubsetProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatPositive.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} UnitProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} VoidProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} ListOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} ListProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} PNat.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatPredicates.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatOperationsProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatDivisor.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatDivisorOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatDivisorProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatGCD.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatGCDEuclid.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} EqualityProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatGCDOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatGCDProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatGCDAlgorithm.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatCoprime.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} PNatOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} Fraction.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FractionBasicOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FractionNormal.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NumRefinements.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} PNatProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NatCoprimeProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FractionBasicProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FractionPredicates.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FractionLTEProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FractionEqProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FractionNormalize.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} FractionNormalizeProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NonNegRational.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NonNegRationalBasicOperations.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NonNegRationalPredicates.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} UniqueProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NonNegRationalBasicProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NonNegRationalLTEProperties.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NonNegRationalMeasures.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} NonNegRationalMeasureProperties

coreTheory: SeqDecProbsCoreTheory.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} SeqDecProbsCoreTheory.lidr

example1: SeqDecProbsExample1.lidr
	${IDRIS} ${IDRIS_COMPILE_FLAGS} SeqDecProbsExample1.lidr -o example1

example1tab: SeqDecProbsExample1tab.lidr
	${IDRIS} ${IDRIS_COMPILE_FLAGS} SeqDecProbsExample1tab.lidr -o example1tab

example2: SeqDecProbsExample2.lidr
	${IDRIS} ${IDRIS_COMPILE_FLAGS} SeqDecProbsExample2.lidr -o example2

example2tab: SeqDecProbsExample2tab.lidr
	${IDRIS} ${IDRIS_COMPILE_FLAGS} SeqDecProbsExample2tab.lidr -o example2tab

example3: SeqDecProbsExample3.lidr
	${IDRIS} ${IDRIS_COMPILE_FLAGS} SeqDecProbsExample3.lidr -o example3

issue3001: NonNegRational3001.lidr
	${IDRIS} ${IDRISFLAGS} NonNegRational3001.lidr

run: example2
	echo "3\n1" | ./example2

profile: profexample
	echo "3\n1" | ./profexample
	gprof profexample gmon.out > profile.txt

clean:
	-find . -name '*.ibc' -delete
