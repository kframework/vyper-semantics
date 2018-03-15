# KVyper: Semantics of Vyper in K

In this repository we present a formal semantics of [Vyper](https://github.com/ethereum/vyper).
For more details, refer to [wiki](https://github.com/kframework/vyper-semantics/wiki).

**WARNING: This repository has not been independently audited for security.  Use with caution.**

## Running KVyper

KVyper can be used to compile Vyper programs to EVM bytecode, being comparable to the production Vyper compiler.

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

Then, build KVyper:
```
$ kompile --syntax-module VYPER-ABSTRACT-SYNTAX vyper-lll/vyper-lll-post.k
$ kompile --syntax-module LLL-EVM-INTERFACE     lll-evm/lll-evm.k
```

Now you can run KVyper (Python 3.6 required):
```
$ python3.6 kvyper.py <pgm>.v.py
```

For example,
```
$ python3.6 kvyper.py tests/examples/token/ERC20.v.py
```

## Contributing to KVyper

To contribute to KVyper: file issues, submit pull requests, and join the
community [K Riot channel](https://riot.im/app/#/room/#k:matrix.org), which
includes a number of K experts.
