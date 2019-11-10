itt: $(shell find -name \*.idr)
	idris -p contrib Main.idr --warnreach --optimise-nat-like-types -o itt
