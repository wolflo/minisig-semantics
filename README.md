# Minisig Semantics
A high-level formal specification of a minimal, gas-optimized multisig contract using [K](https://github.com/kframework/k).
See the [minisig](https://github.com/wolflo/minisig) monorepo.

This is intended partially as an experiment in design-level specification of smart contracts.
Specifying the business logic of a contract in a precise, unambiguous language forces the consideration of edge cases that would otherwise be discovered either in the process of implementing the design or while writing an exploit postmortem.

Building this model in K has several advantages.
The semantics is executable, so the model itself can be tested and used for direct comparison with an implementation.
The semantics is high-level, meaning details of the implementation language, the Ethereum Virtual Machine, and necessary optimizations can be ignored or abstracted away.
It also allows for direct refinement from a high-level K specifcation to an EVM-level specification that can be used to verify correctness properties of the implementation at the bytecode level.
Without a precise definition of correctness, verification of the bytecode is far more difficult.

## Usage
* `docker pull runtimeverificationinc/kframework-k:ubuntu-bionic-c305b58`
* `docker run -it -v ${PWD}:/home/user runtimeverificationinc/kframework-k:ubuntu-bionic-c305b58 /bin/bash`
    * `cd home/user`
    * `make build-all`
    * `make test`
