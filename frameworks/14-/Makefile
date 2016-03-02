IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects --warnreach

all:
	find . -not \( -path "./zombies" -prune \) -not \( -path "./unused" -prune \) -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} --check -V

rv_example: SeqDecProbMonadicTheoryRVExample2.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicTheoryRVExample2.lidr -o rv_example

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
