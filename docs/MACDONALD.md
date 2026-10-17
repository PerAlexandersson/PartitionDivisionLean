# Macdonald layer: design

Nothing in this note is formalized yet. It records which Macdonald-polynomial facts the
partition-division proof uses, how we plan to define the polynomials in Lean, and which
standard inputs we can avoid. Issue #9 has the discussion; the implementation issues are
linked from the roadmap (#15).

## Setting

We work in `N` variables throughout, never in the stable ring of symmetric functions.

- Base field `K = FractionRing (MvPolynomial (Fin 2) ℚ)`, with parameters `q` and `t`.
- Indices: weakly decreasing vectors `λ : Fin N → ℕ` (partitions with at most `N` parts),
  ordered by dominance.
- `D = D_N^1 = Σ_i A_i(x;t) T_{q,x_i}`, where `A_i = ∏_{j ≠ i} (t x_i − x_j)/(x_i − x_j)` and
  `T_{q,x_i}` substitutes `q x_i` for `x_i`. We define `D` without fractions through the
  Vandermonde product `a_δ`: `a_δ · D f = Σ_i (T_{t,x_i} a_δ)(T_{q,x_i} f)` for symmetric `f`.
  This uses divisibility of antisymmetric polynomials by `a_δ`.

## Definition

`P_λ` is the unique symmetric polynomial `m_λ + (dominance-lower m_μ)` that is an eigenvector of
`D`. Here `D` is triangular on the monomial basis with diagonal `Σ_i q^{λ_i} t^{N−i}`, and these
values are distinct for generic `q, t` (Macdonald, *Symmetric Functions and Hall Polynomials*,
Ch. VI §3–4). Existence and uniqueness are finite linear algebra.

## Facts used, and how we get them

| Fact | Plan |
|---|---|
| `D` preserves symmetric polynomials; triangular on `msymm` with the diagonal above | prove (alternant computation) |
| `P_{(1^r)} = e_r` | immediate: `m_{(1^r)}` is dominance-minimal |
| vertical Pieri rule `e_r P_μ = Σ ψ'_{λ/μ} P_λ`, with `ψ'` in row-pair form (Borodin–Corwin, *Macdonald processes*, eq. (2.12)) | prove; the main Macdonald theorem; route under design |
| regularity of `P_λ` at `q = ζ` (primitive `k`-th root, `t` generic) | from Pieri: expand `e_{λ'}`; the coefficient of `P_λ` is `1`, every other term is lower, and every `ψ'` is regular at `q = ζ`. Induct on dominance. No integrality of `J = c_λ P_λ` needed |
| `P_{(k^h)}(ζ, t) = e_h(x_1^k, …, x_N^k)` | eigenvalue argument: at `q = ζ`, `D` fixes `m_{(k^h)}` up to `[N]_t`, and no dominance-lower `P_α(ζ,t)` has that eigenvalue. No branching rule needed |
| periodicity of `ψ'(ζ, t)` under `λ ↦ λ + k(1^h)`, and vanishing on newly legal strips | elementary, from the row-pair form |
| `P_{τ + kξ}(ζ, t) = e_{ξ'}(x^k) · P_τ(ζ, t)` and the free basis indexed by `k`-restricted `τ` | shift operator commuting with every `e_r` |
| positivity of the specialized transition weights | evaluate the cancelled row-pair factors at `t = ζ v`, `v = 1` |

Not needed on the main line: the scalar product, `Q`, `Q'`, `J`, plethysm, `ω`-duality, the
branching rule, and the Descouens–Morita factorization theorem. Descouens–Morita (EJC 29 (2008)
395–410) remains a possible independent cross-check.

## Specialization

Specialization `q ↦ ζ` is a ring map from the localization of `ℚ(t)[q]` at the cyclotomic prime
`Φ_k(q)` to `ℚ(ζ)(t)`. Statements carry explicit membership in that local ring; we never use
analytic limits.

## References

- I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford, 1995, Ch. VI.
- A. Borodin and I. Corwin, Macdonald processes, *Probab. Theory Related Fields* 158 (2014),
  225–400, arXiv:1111.4408.
- F. Descouens and H. Morita, Factorization formulas for Macdonald polynomials, *European J.
  Combin.* 29 (2008), 395–410, arXiv:math/0611522.
- P. Alexandersson and L. Dai, Partition division maps, symmetric functions and positivity,
  arXiv:2604.25440.
