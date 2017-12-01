#!/usr/bin/env bash
set -e      # Exit immediately if any command fails
set -u      # Using undefined variables is an error. Exit immediately

die() { echo -e "FATAL:" "$@"; exit 1; }
type krun >/dev/null || die 'krun not in $PATH'

cmd="$(basename "$0")"
dir="$(dirname "$0")"/..
[[ "$#" == '0' ]] && die "usage: $cmd <pgm>.v.py"

pgm="$1"
ast="$pgm".ast
lll="$pgm".lll

python3 "$dir"/scripts/viper_parser.py "$pgm" >"$ast"
krun -d "$dir"/viper-lll "$ast" | sed 's/.*<lll> \(.*\) <\/lll>.*/\1/' >"$lll"
krun -d "$dir"/lll-evm   "$lll" | sed 's/.*<evm> ListItem ( \(.*\) ) <\/evm>.*/\1/' | sed 's/ ) ListItem ( / /g' | \
python3 "$dir"/scripts/op2byte.py
