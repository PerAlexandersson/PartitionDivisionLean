import Mathlib

/-!
# Challenge: human-auditable statements of the partition-division theorem

This file imports only Mathlib. To audit the formalization, read this file and check that each
definition and statement says what it claims. A passing comparator run (`verify.sh`, or the
Comparator CI workflow) then guarantees that the PartitionDivision library proves exactly these
statements, re-checked by the Lean kernel and the independent `nanoda` kernel, using only the
axioms `propext`, `Quot.sound` and `Classical.choice`.

Symmetric functions are modelled as power series in countably many variables `x_0, x_1, …`
(`MvPowerSeries ℕ ℤ`); see https://www.symmetricfunctions.com/standardSymmetricFunctions.htm
for the standard definitions.
-/

noncomputable section

open Finset

namespace Comparator

section Definitions

variable (σ) (R : Type*) [CommSemiring R]

/-- The elementary symmetric series `e_r = Σ_{|S| = r} x^S`: the coefficient of `x^d` is one when
`d` is squarefree of degree `r`, and zero otherwise. -/
def esymmSeries (r : ℕ) : MvPowerSeries σ R := by
  classical
  exact fun d ↦ if (∀ i, d i ≤ 1) ∧ d.degree = r then 1 else 0

/-- The elementary symmetric series `e_μ = Π_i e_{μ_i}` of a partition. -/
def esymmSeriesPart {n : ℕ} (mu : n.Partition) : MvPowerSeries σ R :=
  (mu.parts.map (esymmSeries σ R)).prod

/-- The monomial symmetric series `m_λ`: the coefficient of `x^d` is one when the nonzero
exponents of `d` form the multiset of parts of `λ`, and zero otherwise. -/
def msymmSeries {n : ℕ} (lam : n.Partition) : MvPowerSeries σ R :=
  fun d ↦ if d.support.val.map d = lam.parts then 1 else 0

/-- The partition-division operator `R_k` on power series: `coeff d (R_k f) = coeff (k • d) f`.
On monomial symmetric functions it is `R_k m_λ = m_{λ/k}` or `0`; see the next two statements. -/
def rowDivSeries (k : ℕ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun f := fun d ↦ f (k • d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Definitions

/-- `R_k` is the operator of the paper, part 1: if every part of `λ` is `k` times the
corresponding part of `ν`, then `R_k m_λ = m_ν`. -/
theorem rowDivSeries_msymmSeries_of_parts_eq {σ R : Type*} [CommSemiring R] {k m n : ℕ}
    (hk : 0 < k) (lam : n.Partition) (nu : m.Partition) (h : lam.parts = nu.parts.map (k * ·)) :
    rowDivSeries σ R k (msymmSeries σ R lam) = msymmSeries σ R nu := by
  sorry

/-- `R_k` is the operator of the paper, part 2: if some part of `λ` is not divisible by `k`,
then `R_k m_λ = 0`. -/
theorem rowDivSeries_msymmSeries_of_not_dvd {σ R : Type*} [CommSemiring R] {k n : ℕ}
    (hk : 0 < k) (lam : n.Partition) (h : ∃ p ∈ lam.parts, ¬ k ∣ p) :
    rowDivSeries σ R k (msymmSeries σ R lam) = 0 := by
  sorry

/-- **The partition-division theorem** (Alexandersson–Dai). For `k ≥ 1` and `μ ⊢ k n`,
`R_k(e_μ)` is a combination of the `e_ν`, `ν ⊢ n`, with natural-number coefficients. -/
theorem exists_nat_esymmSeries_expansion_rowDivSeries {k n : ℕ} (hk : 0 < k)
    (mu : (k * n).Partition) :
    ∃ c : n.Partition → ℕ,
      rowDivSeries ℕ ℤ k (esymmSeriesPart ℕ ℤ mu) =
        ∑ nu, (c nu : ℤ) • esymmSeriesPart ℕ ℤ nu := by
  sorry

/-- **The partition-division theorem in `N ≥ n` variables**, with Mathlib's elementary symmetric
polynomials: the coefficient of `x^d` in `Σ_ν c_ν e_ν` equals the coefficient of `x^{k d}` in
`e_μ`, i.e. `R_k(e_μ) = Σ_ν c_ν e_ν` in `N` variables. -/
theorem exists_nat_esymmPart_expansion_of_le {N k n : ℕ} (hk : 0 < k) (hn : n ≤ N)
    (mu : (k * n).Partition) :
    ∃ c : n.Partition → ℕ, ∀ d : Fin N →₀ ℕ,
      (∑ nu, c nu • MvPolynomial.esymmPart (Fin N) ℤ nu).coeff d =
        (MvPolynomial.esymmPart (Fin N) ℤ mu).coeff (k • d) := by
  sorry

end Comparator
