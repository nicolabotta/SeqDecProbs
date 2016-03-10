IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects -V

all:
	find . -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} -i .. --check

example:
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1206_CylinderExample1.lidr -o example

run: example
	echo "3\n1" | ./example

knapsack:
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1106_KnapsackExample.lidr  -o DynamicProgramming/knapsack.exe

cylinder1:
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1206_CylinderExample1.lidr -o DynamicProgramming/cylinder1.exe

cylinder4:
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1206_CylinderExample4.lidr -o DynamicProgramming/cylinder4.exe

clean:
	-rm example
	-find . -name '*.ibc' -delete
