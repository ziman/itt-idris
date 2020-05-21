ITT = build/exec/itt

.PHONY: clean check install all

all: $(ITT)

$(ITT): $(shell find -name \*.idr) itt.ipkg
	idris2 --build itt.ipkg

install: $(ITT)
	idris2 --install itt.ipkg

examples/%.out: examples/%.itt $(ITT)
	$(ITT) $< > $@

check: $(wildcard examples/*.out)

clean:
	idris2 --clean itt.ipkg
	-rm -rf build
