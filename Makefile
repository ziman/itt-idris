.PHONY: clean

all: build/exec/itt

build/exec/itt: $(shell find -name \*.idr) itt.ipkg
	idris2 --build itt.ipkg

install: build/exec/itt
	idris2 --install itt.ipkg

clean:
	-rm -rf build
