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
| Symmetric functions (countably many variables, as power series over `ℤ`) | `PartitionDivision.exists_nat_esymmSeries_expansion_rowDivSeries` in `PartitionDivision/Division/SymmetricFunction.lean` |
| `R_k` agrees with the definition above: `R_k(m_λ) = m_(λ/k)` or `0` | `rowDivSeries_msymmSeries_of_parts_eq`, `rowDivSeries_msymmSeries_of_not_dvd` (same file) |
| `N` variables, for every `N ≥ n` | `PartitionDivision.exists_nat_esymm_expansion_exponentDiv_esymmPart` in `PartitionDivision/Division/Main.lean` |

The Macdonald-polynomial input is proved in this repository as well; nothing is
assumed. The module layout is in [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md),
and [`docs/PROOF_OUTLINE.md`](docs/PROOF_OUTLINE.md) maps every proof step to its
Lean module.

## Relation to the manuscript proof

The Lean proof follows the manuscript's architecture: the decomposition into
`k`-restricted states, a Macdonald basis at a primitive `k`-th root of unity
`q = ζ` with `t = ζv`, the Pieri transition matrices, the trace identity via the
root-of-unity filter, and positivity of the transition weights at `v = 1`
followed by integrality. It deviates in the following places. These are changes
of route, not of the theorem.

1. **Definition of the Macdonald polynomials.** In `N` variables, `P_λ` is
   defined over `ℚ(q,t)` as the unique eigenvector of Macdonald's operator
   `D_N^1` of the form `m_λ` plus terms lower in *lexicographic* order
   (`MvPolynomial.macdonaldP`, `PartitionDivision/Macdonald/Basic.lean`).
   Macdonald's book uses dominance order. It is a well-known theorem that the two
   definitions agree, since dominance-lower terms are lex-lower and the
   lex-unitriangular eigenvector is unique. The Lean proof does not use that
   agreement and does not formalize it.
2. **The vertical Pieri rule** `e_r P_μ = Σ ψ'_(λ/μ) P_λ` is proved in Lean, not
   cited. The proof follows Macdonald, *Symmetric Functions and Hall Polynomials*,
   Ch. VI §6, in finitely many variables:
   - the operators `D_N^r` are self-adjoint for the `q,t`-pairing;
   - hence `P_λ` is a joint eigenvector of every `D_N^r`;
   - evaluation symmetry and the principal specialization follow;
   - the coefficient is then the row-pair form of `ψ'` (Borodin–Corwin, eq. (2.12)).

   The kernel identity behind self-adjointness was proved by
   [Aristotle](https://aristotle.harmonic.fun). See [`docs/PIERI.md`](docs/PIERI.md).
3. **Regularity at `q = ζ`** is derived from the Pieri rule (every Pieri
   denominator stays nonzero at `q = ζ`), instead of from polynomiality of the
   integral form `J_λ`.
4. **The rectangle values** `P_(k^h)(x; ζ, t) = e_h(x_1^k, …, x_N^k)` are derived
   from the eigenvalues of `D_N^1` at `q = ζ`, instead of from the branching
   rule.
5. **The root-of-unity factorization** `P_(τ+kξ) = e_(ξ')(x^k) P_τ` uses the
   manuscript's shift-operator argument. The Descouens–Morita factorization
   theorem is not used.
6. **The trace identity** is proved for an abstract family of multiplication
   matrices and contains no Macdonald theory. The specialization `t = ζv`,
   `v → 1` is evaluation in the local ring at `v = 1`, not an analytic limit.
7. **Nonvanishing of the principal specialization** `P_λ(t^(N-1), …, 1) ≠ 0` is
   obtained by specializing to `q = t`, where the Macdonald polynomials become
   Schur polynomials.

Details and declaration names are in [`docs/MACDONALD.md`](docs/MACDONALD.md),
[`docs/PIERI.md`](docs/PIERI.md) and the source map in `docs/PROOF_OUTLINE.md`.

## Reused code

Schur polynomials, Kostka numbers, hooks and vertical strips are ported from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) (Apache-2.0) under
`PartitionDivision/TauCeti/`. A few `msymm` lemmas are ported from
[RealRooted](https://github.com/PerAlexandersson/RealRooted). See
[`CREDITS.md`](CREDITS.md). Several proofs were found by Aristotle (Harmonic) and
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
