#!/usr/bin/env bash
set -e      # Exit immediately if any command fails
set -u      # Using undefined variables is an error. Exit immediately

die() { echo -e "FATAL:" "$@"; exit 1; }
type kompile >/dev/null || die 'kompile not in $PATH'

dir="$(dirname $0)"

set -x
kompile --syntax-module VIPER-ABSTRACT-SYNTAX "$dir"/viper-lll/viper-lll-post.k
kompile --syntax-module LLL-EVM-INTERFACE     "$dir"/lll-evm/lll-evm.k
