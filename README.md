# KViper: Semantics of Viper in K

In this repository we present a formal semantics of [Viper](https://github.com/ethereum/viper).
For more details, refer to [wiki](https://github.com/kframework/viper-semantics/wiki).

## Running KViper

KViper can be used to compile Viper programs to EVM bytecodes, being comparable to the production Viper compiler.

First, build KViper:
```
$ ./build.sh
```

Then, run KViper:
```
$ ./bin/kviper.sh <pgm>.v.py
```

For example,
```
$ ./bin/kviper.sh tests/examples/token/ERC20.v.py
```
