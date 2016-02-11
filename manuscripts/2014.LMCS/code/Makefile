IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects

all:
	find . -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} -i .. --check

example:
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1206_CylinderExample1.lidr -o example

run: example
	echo "3\n1" | ./example

examples:
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1106_KnapsackExample.lidr  -o DynamicProgramming/S1106_KnapsackExample.exe
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1206_CylinderExample1.lidr -o DynamicProgramming/S1206_CylinderExample1.exe
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1206_CylinderExample4.lidr -o DynamicProgramming/S1206_CylinderExample4.exe

clean:
	-rm example
	-find . -name '*.ibc' -delete
