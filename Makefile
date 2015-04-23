example:
	idris -p contrib -p effects SeqDecProbMonadicTheoryExample2.lidr -o example

run: example
	echo "3\n1" | ./example

all:
	find . -name '*.lidr' | xargs -n 1 idris -p contrib -p effects --check
