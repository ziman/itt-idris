itt: $(shell find -name \*.idr)
	idris -p contrib Main.idr --optimise-nat-like-types -o itt
