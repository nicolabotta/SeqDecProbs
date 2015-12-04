IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects

all:
	find . -not \( -path "./zombies" -prune \) -not \( -path "./unused" -prune \) -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} --check

example: SeqDecProbMonadicTheoryExample2.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicTheoryExample2.lidr -o example

rv_example: SeqDecProbMonadicTheoryRVExample2.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicTheoryRVExample2.lidr -o rv_example

rv_example_b: SeqDecProbMonadicTheoryRVExample2b.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicTheoryRVExample2b.lidr -o rv_example_b

small_example: SeqDecProbMonadicSmallTheoryExample2.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicSmallTheoryExample2.lidr -o small_example

small_rv_example: SeqDecProbMonadicSmallTheoryRVExample2.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicSmallTheoryRVExample2.lidr -o small_rv_example

small_v_example: SeqDecProbMonadicSmallTheoryVExample2.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicSmallTheoryVExample2.lidr -o small_v_example

profexample: SeqDecProbMonadicSmallTheoryExample2.lidr
	IDRIS_CFLAGS="-pg" ${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicSmallTheoryExample2.lidr -o profexample

run: example
	echo "3\n1" | ./example

profile: profexample
	echo "3\n1" | ./profexample
	gprof profexample gmon.out > profile.txt

clean:
	-rm -f example
	-rm -f rv_example
	-rm -f small_example
	-rm -f small_rv_example
	-rm -f small_v_example
	-rm -f profexample
	-find . -name '*.ibc' -delete
