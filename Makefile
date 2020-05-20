.PHONY: clean

all: build/exec/itt

build/exec/itt: $(shell find -name \*.idr)
	idris2 -p contrib Compiler/Main.idr -o itt

clean:
	-rm -rf build
