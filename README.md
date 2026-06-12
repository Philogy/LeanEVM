This repository contains an executable formal model of the EVM in Lean 4.

Everything here is work in progress and is subject to change.

# Requirements
- Rust (cargo) — builds `tools/evmrs`, the native helper the conformance
  runner shells out to (built automatically by `lake build`).

# Project structure

## Primops
The `Operation` type describing all of the primitive operations:
```
Evm/Operations.lean
```

## EVM
The 256-bit word type (eight 32-bit limbs, proven equivalent to `BitVec 256`):
```
Evm/UInt256.lean
```

The world state and the interpreter's execution state:
```
Evm/State.lean
Evm/ExecutionState.lean
```

The semantic functions (`Υ`, `Θ`, `Lambda`, `X`, `step`):
```
Evm/Semantics.lean
Evm/Step.lean
```

Gas accounting and precompiled contracts:
```
Evm/Gas.lean
Evm/Precompiles.lean
```

## Conformance testing
A git submodule with EVM conformance tests is in:
```
EthereumTests/
```

The test running infrastructure can be found in:
```
Conform/
```

To execute conformance tests, make sure the `EthereumTests` directory is the
appropriate git submodule and run:
```
lake test -- <NUM_THREADS>
```
where `<NUM_THREADS>` is the number of threads running conformance tests in
parallel (`nproc` does not exist on macOS, so always pass it explicitly).

A second argument substring-filters fixture file paths, which is the
recommended way to run quick samples while iterating:
```
lake exe conform 8 stMemoryTest
```
