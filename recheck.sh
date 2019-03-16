#!/bin/bash

echo "[+] compiling itt"
idris -V -p contrib Main.idr -o itt

cd examples
for i in *.itt; do
	echo "[+] checking ${i}"
	../itt "$i" > "${i%.itt}.out"
done
