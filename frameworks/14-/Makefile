IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects --warnreach -V
IDRIS_CHECK_FLAGS = -p contrib -V --check
IDRIS_COMPILE_FLAGS = -p contrib -p effects -V

all:
	find . -not \( -path "./zombies" -prune \) -not \( -path "./unused" -prune \) -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} --check

coreTheory: SeqDecProbsCoreTheory.lidr
	${IDRIS} ${IDRIS_CHECK_FLAGS} SeqDecProbsCoreTheory.lidr

example1: SeqDecProbsExample1.lidr
	${IDRIS} ${IDRIS_COMPILE_FLAGS} SeqDecProbsExample1.lidr -o example1

example1.1: SeqDecProbMonadicExample1.1.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicExample1.1.lidr -o example1.1

example2: SeqDecProbMonadicExample2.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicExample2.lidr -o example2

example3: SeqDecProbMonadicExample3.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicExample3.lidr -o example3

issue3001: NonNegRational3001.lidr
	${IDRIS} ${IDRISFLAGS} NonNegRational3001.lidr

run: example2
	echo "3\n1" | ./example2

profile: profexample
	echo "3\n1" | ./profexample
	gprof profexample gmon.out > profile.txt

clean:
	-find . -name '*.ibc' -delete
