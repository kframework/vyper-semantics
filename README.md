# Semantics of Viper in K


### Example Runs

Viper to LLL:
```
$ cd viper-lll
$ kompile --syntax-module VIPER-ABSTRACT-SYNTAX viper-lll-post.k
$ krun ../tests/examples/token/ERC20.v | sed 's/.*<lll> \(.*\) <\/lll>.*/\1/' | diff - ../tests/examples/token/ERC20.v.lll
```

LLL to EVM:
```
$ cd lll-evm
$ kompile --syntax-module LLL-EVM-INTERFACE lll-evm.k
$ krun ../tests/examples/token/ERC20.v.lll | diff - ../tests/examples/token/ERC20.v.lll.out
```
