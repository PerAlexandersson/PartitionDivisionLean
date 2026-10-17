# Partition division in Lean

This repository is for a Lean formalization of the elementary-positivity
theorem for partition division, proved in a manuscript by Per Alexandersson
and Lilan Dai. It currently contains a [proof outline](docs/PROOF_OUTLINE.md),
not a completed Lean proof.

For a positive integer `k`, partition division sends a monomial symmetric
function `m_λ` to `m_(λ/k)` when every part of `λ` is divisible by `k`, and to
zero otherwise. The target theorem says that `R_k(e_μ)` is a nonnegative
integer combination of elementary symmetric functions for every partition
`μ` of size divisible by `k`.

The outline separates the finite operator and trace argument from its main
missing library input: Macdonald-polynomial factorization and Pieri rules at
a root of unity. No theorem in this repository is currently certified by Lean.

## References

- P. Alexandersson and L. Dai,
  [*Partition Division Maps, Symmetric Functions and Positivity*](https://arxiv.org/abs/2604.25440)
  (2026), for the operator and original conjecture.
- F. Descouens and H. Morita,
  [*Factorization formulas for Macdonald polynomials*](https://doi.org/10.1016/j.ejc.2007.02.013),
  *European Journal of Combinatorics* **29** (2008), 395–410, for the
  root-of-unity factorization used by the manuscript proof.

The companion positivity manuscript is in preparation and is not mirrored here.
