IDRIS = idris
IDRISFLAGS = -p contrib -p effects -i ..

all:
	find . -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} --check

standardDivMod: standardDivMod.lidr
	${IDRIS} ${IDRISFLAGS} standardDivMod.lidr -o standardDivMod

nicolaDivMod: nicolaDivMod.lidr
	${IDRIS} ${IDRISFLAGS} nicolaDivMod.lidr -o nicolaDivMod

melvarDivMod: melvarDivMod.lidr
	${IDRIS} ${IDRISFLAGS} melvarDivMod.lidr -o melvarDivMod

clean:
	-rm -f standardDivMod
	-rm -f nicolaDivMod
	-rm -f melvarDivMod
	-find . -name '*.ibc' -delete
