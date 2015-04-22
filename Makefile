example:
	idris -p contrib -p effects SeqDecProbMonadicTheoryExample2.lidr -o example

run: example
	echo "3\n1" | ./example
