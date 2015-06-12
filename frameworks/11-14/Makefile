all:
	find . -name '*.lidr' | xargs -n 1 idris +RTS -K32000000 -RTS -i .. -p contrib -p effects --check

examples:
	idris +RTS -K32000000 -RTS -p contrib -p effects DynamicProgramming/S1106_Knapsack.lidr -o S1206_Knapsack.exe
	idris +RTS -K32000000 -RTS -p contrib -p effects DynamicProgramming/S1309_Example2.lidr -o S1309_Example2.exe
