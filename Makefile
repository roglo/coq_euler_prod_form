TARGET=Formula.vo Totient.vo QuadRes.vo Ring2.vo Rsummation.vo Rpolynomial2.vo FourSquareEuler.vo FourSquareLag.vo
FILESFORDEP=`LC_ALL=C ls *.v`

all: $(TARGET)

clean:
	rm -f *.glob *.vo *.cm[iox] *.out *.o *.vok *.vos
	rm -f .*.bak .*.aux .*.cache

depend:
	mv .depend .depend.bak
	coqdep $(FILESFORDEP) | LC_ALL=C sort > .depend

.SUFFIXES: .v .vo

.v.vo:
	coqc $<

.PHONY: all clean depend

include .depend
