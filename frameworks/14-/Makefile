IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects

all:
	find . -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} --check

example: SeqDecProbMonadicSmallTheoryExample2.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicSmallTheoryExample2.lidr -o example

exampleRV: SeqDecProbMonadicSmallTheoryRVExample2.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicSmallTheoryRVExample2.lidr -o exampleRV

exampleV: SeqDecProbMonadicSmallTheoryVExample2.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicSmallTheoryVExample2.lidr -o exampleV

profexample: SeqDecProbMonadicSmallTheoryExample2.lidr
	IDRIS_CFLAGS="-pg" ${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicSmallTheoryExample2.lidr -o profexample

run: example
	echo "3\n1" | ./example

profile: profexample
	echo "3\n1" | ./profexample
	gprof profexample gmon.out > profile.txt

clean:
	-rm -f example
	-rm -f exampleRV
	-rm -f exampleV
	-rm -f profexample
	-find . -name '*.ibc' -delete
