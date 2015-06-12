all:
	find . -name '*.lidr' | xargs -n 1 idris +RTS -K32000000 -RTS -i .. -p contrib -p effects --check

example:
	idris +RTS -K32000000 -RTS -p contrib -p effects DynamicProgramming/S1206_Example1.lidr -o example

run: example
	echo "3\n1" | ./example
