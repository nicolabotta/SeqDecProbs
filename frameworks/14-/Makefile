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
