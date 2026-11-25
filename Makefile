TARGET=Formula.vo Totient.vo QuadRes.vo Ring2.vo Rsummation.vo Rpolynomial2.vo FourSquareEuler.vo FourSquareLag.vo FermatTwoSquares.vo
FILESFORDEP=`LC_ALL=C ls *.v`

all: $(TARGET)

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o *.vok *.vos
	rm -f .*.bak .*.aux .*.cache

depend:
	mv .depend .depend.bak
	coqdep -worker aaaa $(FILESFORDEP) | sed 's/ aaaa//' | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	rocq compile $<

.PHONY: all clean depend

include .depend
