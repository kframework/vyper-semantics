# KViper: Semantics of Viper in K

In this repository we present a formal semantics of [Viper](https://github.com/ethereum/viper).
For more details, refer to [wiki](https://github.com/kframework/viper-semantics/wiki).

## Running KViper

KViper can be used to compile Viper programs to EVM bytecodes, being comparable to the production Viper compiler.

First, build K:
```
$ git submodule update --init k
$ cd k
$ mvn package -DskipTests
```
and add the bin directory to your path:
```
$ export PATH="`pwd`/k-distribution/target/release/k/bin:$PATH"
```

Then, build KViper:
```
$ kompile --syntax-module VIPER-ABSTRACT-SYNTAX viper-lll/viper-lll-post.k
$ kompile --syntax-module LLL-EVM-INTERFACE     lll-evm/lll-evm.k
```

Now you can run KViper (Python 3.6 required):
```
$ python3.6 kviper.py <pgm>.v.py
```

For example,
```
$ python3.6 kviper.py tests/examples/token/ERC20.v.py
```
