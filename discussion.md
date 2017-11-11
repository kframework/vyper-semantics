# Discussion

## Viper language design issue

We found that Viper language is tied too much to EVM, inevitably inheriting the limitations of EVM. We stongly believe that such a high-level language as Viper should have a standalone, abstract semantics that is separate from its instantiation (i.e., translation) to its low-level target language(s) such as EVM. This helps to understand and reason about the language semantics in the proper level, as well as make it easier to apply the language to different targets. Also, this separation of concerns will help to formally verify Viper programs. One can verify the high-level logic of the smart contract in the right level of abstraction, and then prove that the Viper program simulates the translated EVM code, i.e., the EVM code does not admit exceptional behaviors (including the EVM-specific low-level exceptions) until they are defined in the original Viper program.

We discuss a couple of specific design issues to be improved.

Address space of maps. A map of Viper is a total function with domain of the entire address space of the local memory, which may lead to conflict between different maps. Currently, Viper simply relies on the hashing scheme to avoid the conflict, hoping the hash collision will not happen, but in theory, it can be broken thus not ultimately reliable. Despite the fact that the probability of the hash collision is very low and if that happens the entire block chain will be broken, we do believe that the language should provide an extra protection layer to completely prevent the conflict even in the presence of the hash collision. For example, monitoring the hashed values can detect the hash collision and the value can be re-hashed with a differnt salt if that happens.

Currently, the internal calls propagate exceptions all the way up to the root callers, which we think is induced by EVM semantics. However, we think that Viper should provide a way of catching those exceptions so that one can have more control of handling those exceptional cases in a secure way.



## ERC20 token verification

TODO:

## Bugs found

While formalizing the lauguage semantics, we found several bugs of Viper compiler, including a critical security vulnerability that is being fixed by Viper team. Those bugs were reported, confirmed, and fixed~\cite{}.

We cannot disclose the security vulnerability until it is fixed. Below we discuss a couple of the other bugs found.
TODO: write-up the security bug

A bug was found in handling typecasting where they failed to insert a runtime check while it should. For example, `as_num256` is typecasting to `num256`, 256-bits unsigned integers, but it is not supposed to typecast a negative value since it will be coerced to a quite different (large) positive number. Viper compiler rejects the invalid typecasting expressions when they can be detected at compiler time, but failed to add the run-time check when they are not. For example, `as_num256(-1)` is rejected at compile-time, but `as_num256(x - y)` was simply compiled to `x - y` even in the case of `x < y`.

Another bug was found in compiling the hash expression, `sha3(e)`. For example, `sha3(0)` is supposed to be translated into EVM code, `PUSH1, 0, PUSH1, 192, MSTORE, PUSH1, 32, PUSH1, 192, SHA3`, which means that the code first stores the value to be hashed, '0', in the local memory at the pre-designated location (here 192), and then computes SHA3 hash of the memory range (with starting location 192 and width 32, i.e., `MEM[192..223]`). But the actually genereated code was: `PUSH1, 0, PUSH1, 192, MSTORE, PUSH1, 192, PUSH1, 32, SHA3` (i.e., `PUSH1 192` and `PUSH1 32` were flipped), which means that it computes SHA3 hash of the wrong memory range (with starting location 32 and witdh 192, i.e., `MEM[32..223]`). This seemingly obvious bug had not been found as the following reason. Fortunately (or unfortunately) the unintended memory range `MEM[32...191]` that is prepended to the value to be hashed (i.e., `MEM[192...223]`) is fixed over all Viper programs. Indeed, they are pre-occupied to store five values of size limits used to clamp values: `ADDRSIZE`, `MAXNUM`, `MINNUM`, `MAXDECIMAL`, `MINDECIMAL`.

 * https://github.com/ethereum/viper/issues/410
 * https://github.com/ethereum/viper/issues/448
 * https://github.com/ethereum/viper/issues/449
 * https://github.com/ethereum/viper/issues/450
 * https://github.com/ethereum/viper/issues/451
 * https://github.com/ethereum/viper/issues/453
