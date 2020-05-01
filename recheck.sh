#!/bin/bash

cd examples
for i in *.itt; do
	echo "[+] checking ${i}"
	../itt "$i" > "${i%.itt}.out"
done
