#!/bin/bash
#
# Instrument a Chez .ss file using trace-lambda.
#
# usage: ./instrument.sh build/exec/itt_app/itt.ss

set -xeuo pipefail

prefix="${2:-}"

sed -e "s/(define \(${prefix}[^ ]*\\) (lambda/(define \\1 (trace-lambda \\1/g" -i "$1"
