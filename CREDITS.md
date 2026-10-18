# Credits

This project reuses Apache-2.0 Lean code from the projects below. Each ported
file keeps its original copyright header and names its source commit in a
provenance line; `docs/ARCHITECTURE.md` describes the porting rules.

| Project | License | Ported files |
|---|---|---|
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Apache-2.0 | dependency, not ported |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | 32 files under `PartitionDivision/TauCeti/` from commit `cebc9b60`, listed below |

Some proofs were found by [Aristotle](https://aristotle.harmonic.fun) (Harmonic) and then ported
and checked locally; the module docstring says so where this applies.

## Tau Ceti files

| Source | License | File |
|---|---|---|
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Algebra/MvPolynomial/Monomial.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Enumerative/Partition/Basic.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Enumerative/Partition/Conjugate.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Enumerative/Partition/Dominance.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Young/BenderKnuth.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Young/BetaNumbers.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Young/Corner.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Young/Diagram.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Young/HookLength/Basic.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Young/Interlacing.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Young/Kostka.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Young/OfRowLens.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Young/Partitions.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Young/SemistandardTableau.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Combinatorics/Young/VerticalStrip.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Data/Fin/StrictAnti.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/Data/Sym/Basic.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/GroupTheory/Perm/SignedDomination.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/LinearAlgebra/BilinearForm/Multilinear.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/LinearAlgebra/Determinant/Basic.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/LinearAlgebra/Multilinear/Span.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/RingTheory/MvPolynomial/Symmetric/Alternant.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/RingTheory/MvPolynomial/Symmetric/Complete.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/RingTheory/MvPolynomial/Symmetric/Homogeneous.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basic.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Basis.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Bialternant.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Branching.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/HsymmPart.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Monomial.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Pieri.lean` |
| [Tau Ceti](https://github.com/TauCetiProject/TauCeti) | Apache-2.0 | `TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/Symmetric.lean` |
