build/exec/itt: $(shell find -name \*.idr)
	idris2 -p contrib Main.idr -o itt
