# Semantics of Viper in K

## Viper Language

Viper is a new experimental language for the smart contracts running on EVM.
It is designed by Ethereum foundation,
supposedly being simpler and more secure language than Solidity
by factoring out the essential components in writing smart contracts,
based on their experience of deploying and operating hundreds of thousands of smart contracts over the last two years.

Specifically, Viper is a kind of object-oriented language
in the sense that a smart contract is represented as a class
whose data fields hold the contract states and methods provide the contract functionalities.
Notably, however, it has no explicit inheritance ---
one of the main design decision made based on their extensive experience of writing smart contracts.
They found that security is more important than programming convenience,
thus the minimality has obvious advantages.

Viper is supposedly a strongly statically typed language that supports type inference.
Types consist of primitive types
(`num` of 128-bits signed integers with overflow exception, `num256` of 256-bits unsigned integers with overflow exception, `decimal` with 128-bits of integer numbers and 10-bits of fractional numbers, `bool`, `address` of 20-bytes, and `bytes32`),
and compound types
(fixed-size arrays, structs, and maps with primitive typed keys).

A local variable has the function scope (i.e., no variable hiding in local blocks)
but no declaration is needed,
although it is questionable from the security perspective of the language design.
It does not allow recursive functions nor unbounded-loops,
but only bounded-loops with break.
It adopts Python syntax, e.g., being white space sensitive.

## Viper Semantics Specification

Specifying Viper language semantics is challenging.
As an experimental language,
Viper does not have a specification document other than the source code of its compiler to EVM,
which also keeps evolving.
Therefore, we took a snapshot ([a886850c1d](https://github.com/ethereum/viper/tree/a886850c1dbdeb3d63639b0dc5b970bd578b0523)) of the latest version of the compiler at the time of writing,
and revealed the semantics via reverse-engineering the source code
as well as communication with the language designers.

Thanks to KEVM,
we were able to specify the Viper language semantics by simply formalizing the compiler translation from Viper to EVM.
Combined with KEVM,
the Viper-to-EVM translation semantics suffices to present the whole semantics of Viper.
This "semantics by translation" approach also helps to emphasize the essence of Viper semantics
by factoring it out from EVM semantics.

We formalized the translation from Viper to EVM.
Our formalization adopted the two-staged translation approach taken by the Viper compiler,
that is, Viper to LLL translation followed by LLL to EVM translation,
where LLL is served an intermediate representation.

Having been originally designed for Solidity compiler,
LLL is a Lisp-like language but much simpler and lower-level than Lisp and closer to EVM.
An LLL expression is an S-expression that is a list of an operator symbol followed by zero or more arguments of another S-expressions.
Part of the LLL operators correspond to the EVM opcodes with the same name.
Only a fragment of LLL is used for the intermediate representation of Viper.


### Viper to LLL translation



The Viper to LLL translation mainly performs the following tasks:
lowering function calls using the ABI encoding;
encoding logical data structures such as structs into byte-array representation (with 32-byte alignment);
allocating memory and storage for each local and state variables, resp.;
inlining builtin-functions;
type checking; and inserting runtime checks for arithemtic overflow.
The control-flow statements are simply translated to that of LLL.

### LLL to EVM translation

The LLL to EVM translation is rather straightforward.
An LLL expression with the EVM opcode is translated to a seqeunce of EVM opcodes
that amounts to evaluating the arguments and pushing the results into the stack in the reverse order followed by the corresponding EVM opcode.
A control-flow operator such as if and repeat is translated in the usual way using the jump opcodes.

