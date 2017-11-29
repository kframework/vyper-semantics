#!/usr/bin/env bash
set -e      # Exit immediately if any command fails
set -u      # Using undefined variables is an error. Exit immediately

cmd="$(basename $0)"
dir="$(dirname $0)"
[[ "$#" == '0' ]] && { echo "usage: $cmd <pgm>.v.py"; exit 1; }

pgm="$1"
ast="$pgm".ast
lll="$pgm".lll

python3 parser/viper_parser.py "$pgm" >"$ast"
krun -d "$dir"/viper-lll "$ast" | sed 's/.*<lll> \(.*\) <\/lll>.*/\1/' >"$lll"
krun -d "$dir"/lll-evm   "$lll" | sed 's/.*<evm> ListItem ( \(.*\) ) <\/evm>.*/\1/' | sed 's/ ) ListItem ( / /g' | python3 "$dir"/lll-evm/opcodes2bytecodes.py
