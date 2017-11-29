#!/usr/bin/env bash

dir="$(dirname $0)"

set -x
kompile --syntax-module VIPER-ABSTRACT-SYNTAX "$dir"/viper-lll/viper-lll-post.k
kompile --syntax-module LLL-EVM-INTERFACE     "$dir"/lll-evm/lll-evm.k
