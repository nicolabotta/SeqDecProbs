IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects --warnreach -V

issue: Fraction.lidr \
       FractionNormal.lidr \
       FractionOperations.lidr \
			 FractionProperties.lidr \
       NatPositive.lidr \
       NonNegRational.lidr \
       NonNegRationalOperations.lidr \
       NonNegRationalProperties.lidr \
       NonNegRationalTest.lidr \
       PNat.lidr \
       PNatOperations.lidr \
       PNatProperties.lidr
	${IDRIS} ${IDRISFLAGS} NonNegRationalTest.lidr

clean:
	-find . -name '*.ibc' -delete
