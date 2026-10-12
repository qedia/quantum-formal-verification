# Qedia: Quantum Program Verification in Lean

A Lean 4 library for quantum mathematics, QHL+, and verified quantum programs.
This repository contains the formal development accompanying our paper.

## Build

Install [elan](https://github.com/leanprover/elan) and Git, then run:

```sh
lake exe cache get
lake build
```

Lean **4.33.0-rc1** and the matching Mathlib revision are pinned in
`lean-toolchain` and `lake-manifest.json`. The default build checks the library,
examples, and tests. Dependencies are downloaded by Lake.

## Imports

```lean
import Qhl.Quantum   -- Quantum mathematics, gates, and arrays
import Qhl.QHLPlus   -- Program semantics, proof systems, and soundness
import Qhl           -- Complete library, including shared register lemmas
import Qhl.Examples  -- Library and verified examples
```

Choose the import needed for your development, or import an individual module.
Library imports do not load examples or tests. `Qhl.Quantum` does not load
program semantics or proof systems. Regression and integration tests have a
separate entry point, `Qhl.Tests`.

| Directory | Contents |
| --- | --- |
| `Qhl/Foundations`, `Qhl/HSpace`, `Qhl/Dirac`, `Qhl/SuperOp` | Quantum states, operators, Dirac notation, and superoperators |
| `Qhl/Gate`, `Qhl/Register` | Gates, quantum arrays, and shared register lemmas |
| `Qhl/Program`, `Qhl/History` | Quantum programs with classical state and their semantics |
| `Qhl/Logic/Source` | `SourceAssertion`, `SourceDerivPar`, `SourceDerivTot`, and soundness |
| `Qhl/Logic` | Reusable proof lemmas and the retained earlier proof systems |
| `Qhl/Examples` | Verified programs and their specifications |
| `Qhl/Tactic` | Supporting tactics |

## Examples

| Example | Main modules in `Qhl/Examples` |
| --- | --- |
| Bell-state preparation | `BellStateTriple` |
| Parallel Hadamard | `ParallelHadamardTriple` |
| QFT | `QFTClassicalTriple`, `QFTComplete` |
| Inverse QFT | `InverseQFTClassicalTriple` |
| QPE | `QPEClassicalTriple` |
| Bounded Repeat-Until-Success | `BoundedRUSTriple`, `RUSZeroBound` |
| Trotter product formula with approximation error | `TrotterTFIMClassicalTriple`, `TrotterTFIMTriple` |
| Cluster-state preparation | `ClusterStateTriple` |
| Bravyi–Kitaev encoding | `BKTransformTriple`, `BKTransformWp` |
| Fermi–Hubbard LCU block encoding | `HubbardLCUTriple`, `HubbardLCUPredicate`, `HubbardExactExpectation` |
| Fermi–Hubbard QSP polynomial transformation | `HubbardQSPBK`, `HubbardQSPSpectral`, `HubbardExactExpectation` |

For example, to build only the bounded RUS example:

```sh
lake build Qhl.Examples.BoundedRUSTriple
```

Each formal theorem states its required assumptions and precise guarantee.

## Verification

With Python 3 installed, run:

```sh
python3 scripts/source_rule_check.py
```

This builds the project and audits the registered source-system proofs,
including their rule dependencies, Lean axioms, program/specification
signatures, and measurement and RUS assertions. The audit covers its explicit
registry of results. Full logs are retained in `.lake/prover-logs/`;
reviewed maintenance warnings are suppressed from routine output.

To reproduce the paper's source line counts:

```sh
python3 scripts/leanwc.py
```

## License

Copyright 2026 Qedia contributors. Licensed under [Apache 2.0](LICENSE).
