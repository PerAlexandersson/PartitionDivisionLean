# Partition division in Lean

A Lean 4 / Mathlib formalization of the elementary-positivity theorem for
partition division, conjectured by Per Alexandersson and Lilan Dai and proved in
their companion manuscript (in preparation, not mirrored here).

For a positive integer `k`, partition division `R_k` sends a monomial symmetric
function `m_λ` to `m_(λ/k)` when every part of `λ` is divisible by `k`, and to
zero otherwise. The theorem: for every `μ ⊢ kn`, `R_k(e_μ)` is a combination of
the `e_ν`, `ν ⊢ n`, with nonnegative integer coefficients.

## Definitions

Standard definitions and properties are as in the
[Symmetric Functions Catalog](https://www.symmetricfunctions.com/), with the notation used here:

- partitions, conjugates, dominance order and hook lengths:
  [preliminaries](https://www.symmetricfunctions.com/preliminaries.htm#prelimPartitions),
  [orderings](https://www.symmetricfunctions.com/preliminaries.htm#partialOrderingsOnPartitions),
  [hooks](https://www.symmetricfunctions.com/preliminaries.htm#partitionCores);
- the ring of symmetric functions, monomial `m_λ` and elementary `e_λ`:
  [symmetric functions](https://www.symmetricfunctions.com/standardSymmetricFunctions.htm#symmetricFunctions),
  [monomial](https://www.symmetricfunctions.com/standardSymmetricFunctions.htm#monomial),
  [elementary](https://www.symmetricfunctions.com/standardSymmetricFunctions.htm#elementaryE);
- Schur polynomials: [Schur](https://www.symmetricfunctions.com/schur.htm#schurS);
- Macdonald polynomials `P_λ(x; q, t)` and their characterization as eigenvectors of Macdonald's
  operators: [Macdonald P](https://www.symmetricfunctions.com/macdonaldP.htm#macdonaldP),
  [eigenvector characterization](https://www.symmetricfunctions.com/macdonaldP.htm#macdonaldPEigenvectors).

## Status

The theorem is **fully checked by Lean**, with no `sorry` and no custom axioms
(only `propext`, `Classical.choice`, `Quot.sound`):

| Statement | Lean declaration |
|---|---|
| Symmetric functions (countably many variables, as power series over `ℤ`) | `PartitionDivision.partitionDivision_ePositive` in `PartitionDivision/Division/SymmetricFunction.lean` |
| `R_k` agrees with the definition above: `R_k(m_λ) = m_(λ/k)` or `0` | `partitionDivision_msymmSeries`, `partitionDivision_msymmSeries_eq_zero` (same file) |
| `N` variables, for every `N ≥ n` | `PartitionDivision.exponentDiv_esymmPart_ePositive` in `PartitionDivision/Division/Main.lean` |
| Walk formula: `k^N c_(μν)` is the weighted number of closed walks on `k`-restricted states | `PartitionDivision.natCast_mul_eq_sum_closedWalks` in `PartitionDivision/Division/WalkFormula.lean` |
| Coloring model: `(∏ μ_i!) R_k(e_μ) = Σ_P X_(G_P)` (chromatic symmetric functions of interval-overlap graphs) | `PartitionDivision.ColoringModel.coloring_identity_esymmPart` in `PartitionDivision/Division/ColoringModel.lean` |

The Macdonald-polynomial input is proved in this repository as well; nothing is
assumed. The module layout is in [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md),
and [`docs/PROOF_OUTLINE.md`](docs/PROOF_OUTLINE.md) maps every proof step to its
Lean module.

## Checking the result

[`comparator/Challenge.lean`](comparator/Challenge.lean) states the theorems with short,
self-contained definitions that import only Mathlib. To audit the formalization, read that file.
The [Comparator CI](.github/workflows/comparator.yml) workflow, or `./verify.sh` locally, runs
[leanprover/comparator](https://github.com/leanprover/comparator). It checks that the library
(`comparator/Solution.lean`) proves exactly those statements, re-checks the proofs with the Lean
kernel and the independent `nanoda` kernel, and allows only the axioms `propext`, `Quot.sound` and
`Classical.choice`.

## Relation to the manuscript proof

The Lean proof follows the current manuscript step by step. Both work with:

- the decomposition into `k`-restricted states;
- the Pieri coefficients in their form indexed by pairs of rows;
- a Macdonald basis at a primitive `k`-th root of unity `q = ζ` with `t = ζv`;
- regularity at `q = ζ` derived from the Pieri rule;
- the rectangle values from the eigenvalues of Macdonald's operator `D_N^1`;
- the shift-operator factorization;
- the trace identity via the root-of-unity filter;
- positivity of the transition weights at `v = 1`, followed by integrality.

The difference is that the manuscript cites standard facts about Macdonald polynomials, and the
Lean development proves them:

1. **Definition.** In `N` variables, `P_λ` is defined over `ℚ(q,t)` as the unique eigenvector of
   `D_N^1` of the form `m_λ` plus lexicographically lower terms (`MvPolynomial.macdonaldP` in
   `PartitionDivision/Macdonald/Basic.lean`). This agrees with Macdonald's definition, where
   dominance order is used: dominance-lower terms are lex-lower, and the lex-unitriangular
   eigenvector is unique. The Lean proof does not need this agreement.
2. **The vertical Pieri rule** `e_r P_μ = Σ ψ'_(λ/μ) P_λ`, with `ψ'` in row-pair form, is proved
   following Macdonald, *Symmetric Functions and Hall Polynomials*, Ch. VI §6, in finitely many
   variables:
   - the operators `D_N^r` are self-adjoint for the finite `q,t`-pairing, so `P_λ` is a joint
     eigenvector of all of them;
   - evaluation symmetry and the principal specialization follow;
   - nonvanishing of the principal specialization is obtained at `q = t`, where the `P_λ` are
     Schur polynomials.

   The `q,t`-kernel identity behind self-adjointness was proved by
   [Aristotle](https://aristotle.harmonic.fun). See [`docs/PIERI.md`](docs/PIERI.md).

The trace identity is proved for any family of multiplication matrices with `P_∅ = 1`, and so
contains no Macdonald theory. Details and declaration names are in
[`docs/MACDONALD.md`](docs/MACDONALD.md), [`docs/PIERI.md`](docs/PIERI.md) and the source map
in [`docs/PROOF_OUTLINE.md`](docs/PROOF_OUTLINE.md).

## Reused code

Schur polynomials, Kostka numbers, hooks and vertical strips are ported from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) (Apache-2.0) under
`PartitionDivision/TauCeti/`; see [`CREDITS.md`](CREDITS.md). Several proofs were found by Aristotle (Harmonic) and
ported; their module docstrings say so.

## Building

Lean/Mathlib v4.35.0. In the workspace use `lake-workspace build PartitionDivision`;
elsewhere, `lake build`.

## References

- P. Alexandersson and L. Dai,
  [*Partition division maps, symmetric functions and positivity*](https://arxiv.org/abs/2604.25440)
  (2026): the operator and the original conjecture.
- I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford
  University Press, 1995, Ch. VI.
- A. Borodin and I. Corwin, Macdonald processes, *Probab. Theory Related Fields*
  **158** (2014), 225–400, [arXiv:1111.4408](https://arxiv.org/abs/1111.4408).
- F. Descouens and H. Morita,
  [*Factorization formulas for Macdonald polynomials*](https://doi.org/10.1016/j.ejc.2007.02.013),
  *European Journal of Combinatorics* **29** (2008), 395–410 (related root-of-unity
  factorization, not used by the Lean proof).
