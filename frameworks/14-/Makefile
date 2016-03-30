IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects --warnreach -V

all:
	find . -not \( -path "./zombies" -prune \) -not \( -path "./unused" -prune \) -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} --check

example1: SeqDecProbMonadicTheoryExample1.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicTheoryExample1.lidr -o example1

example1.1: SeqDecProbMonadicTheoryExample1.1.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicTheoryExample1.1.lidr -o example1.1

example2: SeqDecProbMonadicTheoryExample2.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicTheoryExample2.lidr -o example2

example3: SeqDecProbMonadicTheoryExample3.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicTheoryExample3.lidr -o example3

issue3001: NonNegRational3001.lidr
	${IDRIS} ${IDRISFLAGS} NonNegRational3001.lidr

run: example2
	echo "3\n1" | ./example2

profile: profexample
	echo "3\n1" | ./profexample
	gprof profexample gmon.out > profile.txt

clean:
	-find . -name '*.ibc' -delete
