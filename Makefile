
all: latc

latc:
	ghc --make  latc_llvm.hs -o latc

clean:
	-rm latc *.o *.hi

.PHONY: all clean
