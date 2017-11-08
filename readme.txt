kompile --syntax-module VIPER-SYNTAX viper-lll.k 
krun tests/examples/token/ERC20.v --output nowrap | sed 's/.*<lll> \(.*\) <\/lll>.*/\1/' | sed 's/ ; .LLLExps//g'

kompile --debug --syntax-module LLL-EVM-INTERFACE lll-evm.k && krun --debug tests/with.v.py.lll | diff - tests/with.v.py.lll.out 
kompile --debug --syntax-module LLL-EVM-INTERFACE lll-evm.k && krun --debug tests/examples/token/ERC20.v.lll | diff - tests/examples/token/ERC20.v.lll.out 
