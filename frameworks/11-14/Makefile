IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects

all:
	find . -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} -i .. --check

example: DynamicProgramming/S1309_Example2.lidr
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1309_Example2.lidr -o example

small_example: DynamicProgrammingSmall/S1309_Example2.lidr
	${IDRIS} ${IDRISFLAGS} DynamicProgrammingSmall/S1309_Example2.lidr -o small_example

profexample: DynamicProgramming/S1309_Example2.lidr
	IDRIS_CFLAGS="-pg" ${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1309_Example2.lidr -o profexample

run: example
	echo "3\n1" | ./example

profile: profexample
	echo "3\n1" | ./profexample
	gprof profexample gmon.out > profile.txt

examples: DynamicProgramming/S1106_Knapsack.lidr \
          DynamicProgramming/S1206_Example2.lidr
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1106_Knapsack.lidr -o S1106_Knapsack.exe
	${IDRIS} ${IDRISFLAGS} DynamicProgramming/S1206_Example2.lidr -o S1206_Example2.exe

clean:
	-rm example
	-rm small_example
	-rm S1106_Knapsack.exe
	-rm S1206_Example2.exe
	-find . -name '*.ibc' -delete
