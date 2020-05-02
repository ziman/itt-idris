build/exec/itt: $(shell find -name \*.idr)
	idris2 -p contrib Compiler/Main.idr -o itt
