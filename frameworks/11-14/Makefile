IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects

all:
	find . -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} -i .. --check

example: DynamicProgramming/S1309_Example2.lidr
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1309_Example2.lidr -o example

profexample: DynamicProgramming/S1309_Example2.lidr
	IDRIS_CFLAGS="-pg" ${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1309_Example2.lidr -o profexample

run: example
	echo "3\n1" | ./example

examples: DynamicProgramming/S1106_Knapsack.lidr \
          DynamicProgramming/S1206_Example2.lidr
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1106_Knapsack.lidr -o S1106_Knapsack.exe
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1206_Example2.lidr -o S1206_Example2.exe

clean:
	-rm example S1106_Knapsack.exe S1206_Example2.exe 
	-find . -name '*.ibc' -delete
