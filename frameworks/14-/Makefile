IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects

all:
	find . -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} --check

example: SeqDecProbMonadicSmallTheoryExample2.lidr
	${IDRIS} ${IDRISFLAGS} SeqDecProbMonadicSmallTheoryExample2.lidr -o example

run: example
	echo "3\n1" | ./example

clean:
	-rm example
	-find . -name '*.ibc' -delete
