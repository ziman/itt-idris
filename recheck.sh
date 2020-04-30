#!/bin/bash

echo "[+] compiling itt"
idris2 -p contrib Main.idr -o itt

cd examples
for i in *.itt; do
	echo "[+] checking ${i}"
	../build/exec/itt "$i" > "${i%.itt}.out"
done
