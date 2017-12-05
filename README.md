# KViper: Semantics of Viper in K

In this repository we present a formal semantics of [Viper](https://github.com/ethereum/viper).
For more details, refer to [wiki](https://github.com/kframework/viper-semantics/wiki).

**WARNING: This repository has not been independently audited for security.  Use with caution.**

## Running KViper

KViper can be used to compile Viper programs to EVM bytecode, being comparable to the production Viper compiler.

First, build K after installing the prerequisites in `k/README.md` (after the first command):
```
$ git submodule update --init k
$ cd k
$ mvn package -DskipTests
```
Add the bin directory [to your path](https://www.java.com/en/download/help/path.xml):
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

## Contributing to KViper

To contribute to KViper: file issues, submit pull requests, and join the 
community [K Riot channel](https://riot.im/app/#/room/#k:matrix.org), which
includes a number of K experts.
