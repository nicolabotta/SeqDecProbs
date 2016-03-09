IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects --warnreach -V

all:
	find . -not \( -path "./zombies" -prune \) -not \( -path "./unused" -prune \) -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} --check

example2: SeqDecProbMonadicTheoryRVExample2.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicTheoryRVExample2.lidr -o example2

run: example2
	echo "3\n1" | ./example2

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
