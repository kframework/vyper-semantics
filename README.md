# KViper: Semantics of Viper in K

In this repository we present a formal semantics of [Viper](https://github.com/ethereum/viper).
For more details, refer to [wiki](https://github.com/kframework/viper-semantics/wiki).

KViper can be used to compile Viper programs to EVM bytecodes.

#### Building KViper

```
$ kompile --syntax-module VIPER-ABSTRACT-SYNTAX viper-lll/viper-lll-post.k
$ kompile --syntax-module LLL-EVM-INTERFACE lll-evm/lll-evm.k
```

#### Running KViper

KViper consists of three components:

 * Generating an AST from a given Viper program
   ```
   $ python parser/viper_parser.py PGM.v.py >PGM.v.ast
   ```
 * Translating from Viper (AST) to LLL
   ```
   $ krun -d viper-lll PGM.v.ast | sed 's/.*<lll> \(.*\) <\/lll>.*/\1/' >PGM.v.lll
   ```
 * Translating from LLL to EVM
   ```
   $ krun -d lll-evm PGM.v.lll | sed 's/.*<evm> ListItem ( \(.*\) ) <\/evm>.*/\1/' | sed 's/ ) ListItem ( / /g' | python lll-evm/opcodes2bytecodes.py
   ```

#### Example Run

```
$ python parser/viper_parser.py tests/examples/token/ERC20.v.py | diff - tests/examples/token/ERC20.v.ast
$ krun -d viper-lll tests/examples/token/ERC20.v.ast | sed 's/.*<lll> \(.*\) <\/lll>.*/\1/' | diff - tests/examples/token/ERC20.v.lll
$ krun -d lll-evm tests/examples/token/ERC20.v.lll | sed 's/.*<evm> ListItem ( \(.*\) ) <\/evm>.*/\1/' | sed 's/ ) ListItem ( / /g' | python lll-evm/opcodes2bytecodes.py
```
