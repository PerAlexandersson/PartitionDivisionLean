/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import PartitionDivision.Macdonald.Pairing

/-!
# The Cauchy kernel of the `(q, t)` pairing

Let `f(z) = ∑ₙ c(n) zⁿ` with `c = MvPolynomial.macdonaldGCoeff q t`, the series of
`(tz; q)_∞ / (z; q)_∞`, and let `Π(x, y) = ∏_{i,j} f(xᵢ yⱼ)` (Macdonald VI (2.10), (4.13)).  This
file provides the parts of Lemma 5 of the Pieri ledger (`docs/PIERI.md`) that do not involve the
Macdonald operators themselves.

## The degree-`d` kernel and its expansion

The coefficient of `x^r y^c` in `Π` is the contingency-table sum
`MvPolynomial.macdonaldKernelCoeff q t r c`.  The degree-`d` part of `Π` is therefore the
polynomial `MvPolynomial.macdonaldKernel σ q t d`, an element of
`MvPolynomial σ (MvPolynomial σ R)`: the outer variables are `x`, the coefficients are polynomials
in `y`.  We prove `Π_d = ∑_λ g_λ(x) m_λ(y)`, the sum over the partitions `λ` of `d` with at most
`|σ|` parts (`MvPolynomial.macdonaldKernel_eq_sum`): this is Macdonald VI (2.21) in finitely many
variables, i.e. `(g_λ)` and `(m_λ)` are dual bases for the kernel.

## The self-adjointness criterion

The symmetric polynomials of degree `d` in `x` and in `y` embed jointly into
`MvPolynomial σ (MvPolynomial σ R)` by `p ⊗ q ↦ p(x) q(y)`
(`MvPolynomial.macdonaldKernelEmbedding`, injective by flatness), and the kernel is the image of
`∑_λ g_λ ⊗ m_λ` (`MvPolynomial.macdonaldKernelEmbedding_sum`).  An endomorphism `A` of the
degree-`d` symmetric polynomials is self-adjoint for `MvPolynomial.macdonaldPairing` if and only if
`A` acting in `x` and `A` acting in `y` agree on the kernel:
`∑_λ A(g_λ)(x) m_λ(y) = ∑_λ g_λ(x) A(m_λ)(y)` (`MvPolynomial.isSelfAdjoint_macdonaldPairing_iff`).
This is a dual-basis computation with `⟨g_λ, m_μ⟩ = δ_{λμ}`.

## The `q`-shift functional equation

As a formal power series in the `2|σ|` variables `σ ⊕ σ` (`Sum.inl i` is `xᵢ`, `Sum.inr j` is
`yⱼ`), `Π = ∏_{i,j} f(xᵢ yⱼ)` is `MvPolynomial.macdonaldKernelSeries`, with each factor
`MvPolynomial.macdonaldKernelFactor` defined by its coefficients.  Its coefficients are the kernel
coefficients (`MvPolynomial.coeff_macdonaldKernelSeries`), so its degree-`d` part is
`MvPolynomial.macdonaldKernel`
(`MvPolynomial.coeff_macdonaldKernelSeries_eq_coeff_macdonaldKernel`).  Let `T_{q,I}` substitute
`q xᵢ` for `xᵢ` for `i ∈ I` (`MvPowerSeries.rescale` by `MvPolynomial.macdonaldShiftScale σ q I`).
The `q`-difference equation of the coefficients gives `f(qz)(1 - tz) = f(z)(1 - z)`, and hence,
with the denominators cleared,

`T_{q,I} Π · ∏_{i ∈ I} ∏_j (1 - t xᵢ yⱼ) = Π · ∏_{i ∈ I} ∏_j (1 - xᵢ yⱼ)`

(`MvPolynomial.rescale_macdonaldKernelSeries_mul`), valid when every `1 - q^{k+1}` is a unit.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter VI,
  (2.10), (2.21), (3.11)--(3.12).
-/

@[expose] public section

open Finset TauCeti Module TensorProduct

namespace MvPolynomial

variable {R : Type*} [CommRing R] {σ : Type*}

section Embedding

variable {d : ℕ}

/-- **The embedding of the tensor square of the symmetric polynomials of degree `d` into the
bivariate polynomials**: `p ⊗ q ↦ p(x) q(y)` in `MvPolynomial σ (MvPolynomial σ R)`, where the
outer variables are `x` and the coefficient polynomials are in `y`
(`MvPolynomial.macdonaldKernelEmbedding_tmul`). -/
noncomputable def macdonaldKernelEmbedding (σ R : Type*) [CommRing R] (d : ℕ) :
    symmetricHomogeneousSubmodule σ R d ⊗[R] symmetricHomogeneousSubmodule σ R d →ₗ[R]
      MvPolynomial σ (MvPolynomial σ R) :=
  ((algebraTensorAlgEquiv R (MvPolynomial σ R)).toAlgHom.restrictScalars R).toLinearMap ∘ₗ
    (TensorProduct.comm R (MvPolynomial σ R) (MvPolynomial σ R)).toLinearMap ∘ₗ
      TensorProduct.map (symmetricHomogeneousSubmodule σ R d).subtype
        (symmetricHomogeneousSubmodule σ R d).subtype

/-- The embedding sends `p ⊗ q` to `p(x) q(y)`. -/
@[simp]
theorem macdonaldKernelEmbedding_tmul (x y : symmetricHomogeneousSubmodule σ R d) :
    macdonaldKernelEmbedding σ R d (x ⊗ₜ y) =
      map C (x : MvPolynomial σ R) * C (y : MvPolynomial σ R) := by
  simp [macdonaldKernelEmbedding, smul_eq_C_mul, algebraMap_eq, mul_comm]

/-- **The embedding `p ⊗ q ↦ p(x) q(y)` is injective**: the symmetric polynomials of degree `d`
form a free, hence flat, module, so tensoring the inclusions stays injective, and
`R[y] ⊗ R[x] ≃ R[y][x]`. -/
theorem macdonaldKernelEmbedding_injective [Finite σ] :
    Function.Injective (macdonaldKernelEmbedding σ R d) := by
  have := Fintype.ofFinite σ
  have : Module.Free R (symmetricHomogeneousSubmodule σ R d) :=
    Module.Free.of_basis (msymmBasis σ R d)
  rw [macdonaldKernelEmbedding, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (algebraTensorAlgEquiv R (MvPolynomial σ R)).injective.comp
    ((TensorProduct.comm R _ _).injective.comp
      (TensorProduct.map_injective_of_flat_flat _ _ (Submodule.injective_subtype _)
        (Submodule.injective_subtype _)))

/-- Injectivity of `MvPolynomial.macdonaldKernelEmbedding`, as an `iff`. -/
theorem macdonaldKernelEmbedding_inj [Finite σ] {x y : symmetricHomogeneousSubmodule σ R d ⊗[R]
      symmetricHomogeneousSubmodule σ R d} :
    macdonaldKernelEmbedding σ R d x = macdonaldKernelEmbedding σ R d y ↔ x = y :=
  macdonaldKernelEmbedding_injective.eq_iff

end Embedding

section Series

variable (σ) in
/-- The exponent of the monomial `xᵢ yⱼ` in the variables `σ ⊕ σ`. -/
noncomputable def macdonaldKernelExponent (i j : σ) : σ ⊕ σ →₀ ℕ :=
  Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1

/-- The exponent of `xᵢ` in `(xᵢ yⱼ)ⁿ` is `n`. -/
theorem macdonaldKernelExponent_inl (i j : σ) (n : ℕ) :
    (n • macdonaldKernelExponent σ i j) (Sum.inl i) = n := by
  simp [macdonaldKernelExponent]

/-- Rescaling the variables by `c` multiplies `(xᵢ yⱼ)ⁿ` by `(c(xᵢ) c(yⱼ))ⁿ`. -/
theorem prod_pow_nsmul_macdonaldKernelExponent (c : σ ⊕ σ → R) (i j : σ) (n : ℕ) :
    ((n • macdonaldKernelExponent σ i j).prod fun s k ↦ c s ^ k) =
      (c (Sum.inl i) * c (Sum.inr j)) ^ n := by
  rw [macdonaldKernelExponent, smul_add, Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
    Finsupp.smul_single, Finsupp.smul_single, Finsupp.prod_single_index (by simp),
    Finsupp.prod_single_index (by simp), mul_pow]
  simp

/-- The monomial `xᵢ yⱼ` does not divide `1`. -/
theorem not_macdonaldKernelExponent_le_zero (i j : σ) :
    ¬macdonaldKernelExponent σ i j ≤ 0 • macdonaldKernelExponent σ i j := by
  intro h
  have := h (Sum.inl i)
  simp [macdonaldKernelExponent] at this

/-- The `x`-exponents of `∏_{i,j} (xᵢ yⱼ)^{A i j}` are the row sums of `A`. -/
theorem sum_nsmul_macdonaldKernelExponent_inl [Fintype σ] (A : σ → σ → ℕ) (i : σ) :
    (∑ p : σ × σ, A p.1 p.2 • macdonaldKernelExponent σ p.1 p.2) (Sum.inl i) = ∑ j, A i j := by
  classical
  rw [Finsupp.finsetSum_apply, Fintype.sum_prod_type]
  simp [macdonaldKernelExponent, Finsupp.single_apply]

/-- The `y`-exponents of `∏_{i,j} (xᵢ yⱼ)^{A i j}` are the column sums of `A`. -/
theorem sum_nsmul_macdonaldKernelExponent_inr [Fintype σ] (A : σ → σ → ℕ) (j : σ) :
    (∑ p : σ × σ, A p.1 p.2 • macdonaldKernelExponent σ p.1 p.2) (Sum.inr j) = ∑ i, A i j := by
  classical
  rw [Finsupp.finsetSum_apply, Fintype.sum_prod_type]
  simp [macdonaldKernelExponent, Finsupp.single_apply]

variable [DecidableEq σ]

variable (σ) in
/-- **The factor `f(xᵢ yⱼ)` of the kernel**, as a power series in the variables `σ ⊕ σ`: its
coefficient at `(xᵢ yⱼ)ⁿ` is `c(n) = MvPolynomial.macdonaldGCoeff q t n`, and all other
coefficients vanish.  A monomial `e` is a power of `xᵢ yⱼ` exactly when `e = e(xᵢ) • (xᵢ yⱼ)`. -/
noncomputable def macdonaldKernelFactor (q t : R) (i j : σ) : MvPowerSeries (σ ⊕ σ) R :=
  fun e ↦ if e = e (Sum.inl i) • macdonaldKernelExponent σ i j then
    macdonaldGCoeff q t (e (Sum.inl i)) else 0

/-- The coefficient of `(xᵢ yⱼ)ⁿ` in `f(xᵢ yⱼ)` is `c(n)`. -/
theorem coeff_nsmul_macdonaldKernelFactor (q t : R) (i j : σ) (n : ℕ) :
    MvPowerSeries.coeff (n • macdonaldKernelExponent σ i j) (macdonaldKernelFactor σ q t i j) =
      macdonaldGCoeff q t n := by
  rw [MvPowerSeries.coeff_apply]
  simp only [macdonaldKernelFactor, macdonaldKernelExponent_inl, ite_eq_left_iff]
  simp

/-- `f(xᵢ yⱼ)` has no coefficients away from the powers of `xᵢ yⱼ`. -/
theorem coeff_macdonaldKernelFactor_of_ne (q t : R) {i j : σ} {e : σ ⊕ σ →₀ ℕ}
    (he : ∀ n : ℕ, e ≠ n • macdonaldKernelExponent σ i j) :
    MvPowerSeries.coeff e (macdonaldKernelFactor σ q t i j) = 0 := by
  rw [MvPowerSeries.coeff_apply]
  simp only [macdonaldKernelFactor]
  exact ite_eq_right (he _)

/-- A rescaling that fixes the product `xᵢ yⱼ` fixes `f(xᵢ yⱼ)`. -/
theorem rescale_macdonaldKernelFactor_of_mul_eq_one (q t : R) (i j : σ) {c : σ ⊕ σ → R}
    (hc : c (Sum.inl i) * c (Sum.inr j) = 1) :
    MvPowerSeries.rescale c (macdonaldKernelFactor σ q t i j) =
      macdonaldKernelFactor σ q t i j := by
  ext e
  rw [MvPowerSeries.coeff_rescale]
  by_cases he : ∃ n : ℕ, e = n • macdonaldKernelExponent σ i j
  · obtain ⟨n, rfl⟩ := he
    rw [prod_pow_nsmul_macdonaldKernelExponent, hc, one_pow, one_mul]
  · push Not at he
    rw [coeff_macdonaldKernelFactor_of_ne q t he, mul_zero]

/-- **The `q`-shift of one factor**: if a rescaling multiplies `xᵢ yⱼ` by `q`, then
`f(q xᵢ yⱼ) (1 - t xᵢ yⱼ) = f(xᵢ yⱼ) (1 - xᵢ yⱼ)`.  This is the `q`-difference equation
`MvPolynomial.one_sub_pow_mul_macdonaldGCoeff_succ`, read coefficientwise. -/
theorem rescale_macdonaldKernelFactor_mul {q : R} (hq : ∀ k, IsUnit (1 - q ^ (k + 1))) (t : R)
    (i j : σ) {c : σ ⊕ σ → R} (hc : c (Sum.inl i) * c (Sum.inr j) = q) :
    MvPowerSeries.rescale c (macdonaldKernelFactor σ q t i j) *
        (1 - MvPowerSeries.monomial (macdonaldKernelExponent σ i j) t) =
      macdonaldKernelFactor σ q t i j *
        (1 - MvPowerSeries.monomial (macdonaldKernelExponent σ i j) 1) := by
  ext e
  rw [mul_sub, mul_sub, mul_one, mul_one, map_sub, map_sub, MvPowerSeries.coeff_mul_monomial,
    MvPowerSeries.coeff_mul_monomial, MvPowerSeries.coeff_rescale]
  by_cases he : ∃ n : ℕ, e = n • macdonaldKernelExponent σ i j
  · obtain ⟨n, rfl⟩ := he
    cases n with
    | zero =>
      rw [ite_eq_right (not_macdonaldKernelExponent_le_zero i j),
        ite_eq_right (not_macdonaldKernelExponent_le_zero i j),
        prod_pow_nsmul_macdonaldKernelExponent, pow_zero, one_mul]
    | succ k =>
      have hle : macdonaldKernelExponent σ i j ≤ (k + 1) • macdonaldKernelExponent σ i j := by
        rw [succ_nsmul]
        exact le_add_self
      have hsub : (k + 1) • macdonaldKernelExponent σ i j - macdonaldKernelExponent σ i j =
          k • macdonaldKernelExponent σ i j := by
        rw [succ_nsmul, add_tsub_cancel_right]
      rw [ite_eq_left hle, ite_eq_left hle, hsub, MvPowerSeries.coeff_rescale,
        prod_pow_nsmul_macdonaldKernelExponent, prod_pow_nsmul_macdonaldKernelExponent, hc,
        coeff_nsmul_macdonaldKernelFactor, coeff_nsmul_macdonaldKernelFactor]
      linear_combination -(one_sub_pow_mul_macdonaldGCoeff_succ hq t k)
  · push Not at he
    have h2 : ∀ hle : macdonaldKernelExponent σ i j ≤ e,
        MvPowerSeries.coeff (e - macdonaldKernelExponent σ i j)
          (macdonaldKernelFactor σ q t i j) = 0 := fun hle ↦
      coeff_macdonaldKernelFactor_of_ne q t fun n hn ↦ he (n + 1) (by
        rw [succ_nsmul, ← hn, tsub_add_cancel_of_le hle])
    rw [coeff_macdonaldKernelFactor_of_ne q t he, mul_zero]
    split_ifs with hle
    · rw [MvPowerSeries.coeff_rescale, h2 hle]
      simp
    · rfl

variable [Fintype σ]

variable (σ) in
/-- **The kernel `Π(x, y) = ∏_{i,j} f(xᵢ yⱼ)`** as a power series in the variables `σ ⊕ σ`. -/
noncomputable def macdonaldKernelSeries (q t : R) : MvPowerSeries (σ ⊕ σ) R :=
  ∏ i, ∏ j, macdonaldKernelFactor σ q t i j

variable (σ) in
/-- The scaling vector of the `q`-shift `T_{q,I}`: `q` at the variables `xᵢ` with `i ∈ I`, and `1`
at all other variables.  `MvPowerSeries.rescale` by it substitutes `q xᵢ` for `xᵢ`, `i ∈ I`. -/
def macdonaldShiftScale (q : R) (I : Finset σ) : σ ⊕ σ → R :=
  Sum.elim (fun i ↦ if i ∈ I then q else 1) fun _ ↦ 1

/-- **The `q`-shift functional equation of the kernel**: for every finset `I` of `x`-variables,
`T_{q,I} Π · ∏_{i ∈ I} ∏_j (1 - t xᵢ yⱼ) = Π · ∏_{i ∈ I} ∏_j (1 - xᵢ yⱼ)`, where `T_{q,I}`
substitutes `q xᵢ` for `xᵢ`, `i ∈ I`.  Factors with `i ∉ I` are unchanged by the shift. -/
theorem rescale_macdonaldKernelSeries_mul {q : R} (hq : ∀ k, IsUnit (1 - q ^ (k + 1))) (t : R)
    (I : Finset σ) :
    MvPowerSeries.rescale (macdonaldShiftScale σ q I) (macdonaldKernelSeries σ q t) *
        ∏ i ∈ I, ∏ j, (1 - MvPowerSeries.monomial (macdonaldKernelExponent σ i j) t) =
      macdonaldKernelSeries σ q t *
        ∏ i ∈ I, ∏ j, (1 - MvPowerSeries.monomial (macdonaldKernelExponent σ i j) 1) := by
  have hin : ∀ i ∈ I,
      (∏ j, MvPowerSeries.rescale (macdonaldShiftScale σ q I) (macdonaldKernelFactor σ q t i j)) *
          ∏ j, (1 - MvPowerSeries.monomial (macdonaldKernelExponent σ i j) t) =
        (∏ j, macdonaldKernelFactor σ q t i j) *
          ∏ j, (1 - MvPowerSeries.monomial (macdonaldKernelExponent σ i j) 1) := fun i hi ↦ by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun j _ ↦ rescale_macdonaldKernelFactor_mul hq t i j (by
      simp [macdonaldShiftScale, hi])
  have hout : ∀ i ∈ Iᶜ,
      ∏ j, MvPowerSeries.rescale (macdonaldShiftScale σ q I) (macdonaldKernelFactor σ q t i j) =
        ∏ j, macdonaldKernelFactor σ q t i j := fun i hi ↦
    prod_congr rfl fun j _ ↦ rescale_macdonaldKernelFactor_of_mul_eq_one q t i j (by
      simp [macdonaldShiftScale, mem_compl.mp hi])
  rw [macdonaldKernelSeries, map_prod]
  simp_rw [map_prod]
  rw [← prod_mul_prod_compl I,
    ← prod_mul_prod_compl I (fun i ↦ ∏ j, macdonaldKernelFactor σ q t i j),
    prod_congr rfl hout, mul_right_comm, ← prod_mul_distrib, prod_congr rfl hin, prod_mul_distrib,
    mul_right_comm]

/-- **The coefficients of the kernel series are the kernel coefficients**: the coefficient of
`x^r y^c` in `∏_{i,j} f(xᵢ yⱼ)` is `MvPolynomial.macdonaldKernelCoeff q t r c`. -/
theorem coeff_macdonaldKernelSeries (q t : R) (r c : σ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.sumElim r c) (macdonaldKernelSeries σ q t) =
      macdonaldKernelCoeff q t ⇑r ⇑c := by
  have hterm (l : σ × σ →₀ σ ⊕ σ →₀ ℕ) :
      ∏ p : σ × σ, MvPowerSeries.coeff (l p) (macdonaldKernelFactor σ q t p.1 p.2) =
        if ∀ p : σ × σ, l p = (l p) (Sum.inl p.1) • macdonaldKernelExponent σ p.1 p.2 then
          ∏ p : σ × σ, macdonaldGCoeff q t ((l p) (Sum.inl p.1)) else 0 := by
    simp only [MvPowerSeries.coeff_apply, macdonaldKernelFactor]
    exact Fintype.prod_ite_zero
  rw [macdonaldKernelSeries, ← Fintype.prod_prod_type', MvPowerSeries.coeff_prod,
    macdonaldKernelCoeff]
  simp_rw [hterm]
  rw [← sum_filter]
  refine sum_nbij' (fun l i j ↦ l (i, j) (Sum.inl i))
    (fun A ↦ Finsupp.equivFunOnFinite.symm fun p ↦ A p.1 p.2 • macdonaldKernelExponent σ p.1 p.2)
    (fun l hl ↦ ?_) (fun A hA ↦ ?_) (fun l hl ↦ ?_) (fun A _ ↦ ?_) fun l _ ↦ ?_
  · simp only [mem_filter, mem_finsuppAntidiag, subset_univ, and_true] at hl
    obtain ⟨hsum, hform⟩ := hl
    have he : Finsupp.sumElim r c =
        ∑ p : σ × σ, (l p (Sum.inl p.1)) • macdonaldKernelExponent σ p.1 p.2 := by
      rw [← hsum]
      exact sum_congr rfl fun p _ ↦ hform p
    simp only [mem_contingencyTables]
    refine ⟨fun i ↦ ?_, fun j ↦ ?_⟩
    · exact (sum_nsmul_macdonaldKernelExponent_inl (fun a b ↦ l (a, b) (Sum.inl a)) i).symm.trans
        (congrArg (· (Sum.inl i)) he).symm
    · exact (sum_nsmul_macdonaldKernelExponent_inr (fun a b ↦ l (a, b) (Sum.inl a)) j).symm.trans
        (congrArg (· (Sum.inr j)) he).symm
  · simp only [mem_contingencyTables] at hA
    simp only [mem_filter, mem_finsuppAntidiag, subset_univ, and_true]
    refine ⟨Finsupp.ext fun s ↦ ?_, fun p ↦ ?_⟩
    · have hs : (∑ p : σ × σ, (Finsupp.equivFunOnFinite.symm fun p : σ × σ ↦
          A p.1 p.2 • macdonaldKernelExponent σ p.1 p.2) p) =
          ∑ p : σ × σ, A p.1 p.2 • macdonaldKernelExponent σ p.1 p.2 :=
        sum_congr rfl fun p _ ↦ by simp
      rw [hs]
      cases s with
      | inl i => rw [sum_nsmul_macdonaldKernelExponent_inl, Finsupp.sumElim_inl, hA.1 i]
      | inr j => rw [sum_nsmul_macdonaldKernelExponent_inr, Finsupp.sumElim_inr, hA.2 j]
    · simp [macdonaldKernelExponent]
  · simp only [mem_filter, mem_finsuppAntidiag, subset_univ, and_true] at hl
    exact Finsupp.ext fun p ↦ by simpa using (hl.2 p).symm
  · funext i j
    simp [macdonaldKernelExponent]
  · exact Fintype.prod_prod_type fun p : σ × σ ↦ macdonaldGCoeff q t (l p (Sum.inl p.1))

end Series

variable [Fintype σ] [DecidableEq σ]

section Kernel

variable (σ) in
/-- **The degree-`d` part `Π_d` of the kernel `∏_{i,j} f(xᵢ yⱼ)`**, as a polynomial in `x` with
coefficients polynomials in `y`: the coefficient of `x^r y^c`, for `|r| = |c| = d`, is the
contingency-table sum `MvPolynomial.macdonaldKernelCoeff q t r c`
(`MvPolynomial.coeff_coeff_macdonaldKernel`). -/
noncomputable def macdonaldKernel (q t : R) (d : ℕ) : MvPolynomial σ (MvPolynomial σ R) :=
  ∑ r ∈ (univ : Finset σ).finsuppAntidiag d, monomial r
    (∑ c ∈ (univ : Finset σ).finsuppAntidiag d, monomial c (macdonaldKernelCoeff q t ⇑r ⇑c))

/-- The coefficient of `x^r y^c` in `Π_d` is the kernel coefficient when `|r| = |c| = d`, and `0`
otherwise. -/
theorem coeff_coeff_macdonaldKernel (q t : R) (d : ℕ) (r c : σ →₀ ℕ) :
    ((macdonaldKernel σ q t d).coeff r).coeff c =
      if r.degree = d ∧ c.degree = d then macdonaldKernelCoeff q t ⇑r ⇑c else 0 := by
  rw [macdonaldKernel, coeff_sum]
  simp only [coeff_monomial, sum_ite_eq', mem_finsuppAntidiag, subset_univ, and_true]
  by_cases hr : r.degree = d
  · rw [ite_eq_left (by rwa [Finsupp.degree_eq_sum] at hr), coeff_sum]
    simp only [coeff_monomial, sum_ite_eq', mem_finsuppAntidiag, subset_univ, and_true, hr,
      true_and, Finsupp.degree_eq_sum]
  · rw [ite_eq_right (by rwa [Finsupp.degree_eq_sum] at hr), ite_eq_right fun h ↦ hr h.1]
    simp

/-- A product `∏ᵢ g_{rᵢ}` over the alphabet is symmetric. -/
theorem prod_macdonaldG_isSymmetric (q t : R) (r : σ → ℕ) :
    (∏ i, macdonaldG σ q t (r i)).IsSymmetric := by
  rw [← mem_symmetricSubalgebra]
  exact Subalgebra.prod_mem _ fun i _ ↦
    (mem_symmetricSubalgebra _).mpr (macdonaldG_isSymmetric q t (r i))

/-- **The kernel expansion** (Macdonald VI (2.21) in finitely many variables):
`Π_d(x, y) = ∑_λ g_λ(x) m_λ(y)`, the sum over the partitions `λ` of `d` with at most `|σ|`
parts. -/
theorem macdonaldKernel_eq_sum (q t : R) (d : ℕ) :
    macdonaldKernel σ q t d = ∑ ν : {ν : d.Partition // ν.parts.card ≤ Fintype.card σ},
      map C (macdonaldGPart σ q t ν.1) * C (msymm σ R ν.1) := by
  ext r c
  have hterm (p m : MvPolynomial σ R) :
      ((map C p * C m).coeff r).coeff c = p.coeff r * m.coeff c := by
    rw [mul_comm, coeff_C_mul, coeff_map, mul_comm, coeff_C_mul]
  rw [coeff_coeff_macdonaldKernel, coeff_sum, coeff_sum]
  simp only [hterm]
  by_cases hc : c.degree = d
  · rw [Finset.sum_eq_single ⟨weightPartition c hc, card_parts_weightPartition_le c hc⟩]
    · rw [TauCeti.coeff_msymm R _ hc, ite_eq_left rfl, mul_one]
      by_cases hr : r.degree = d
      · rw [ite_eq_left ⟨hr, hc⟩]
        set la := weightPartition c hc
        have hla : la.parts.card ≤ Fintype.card σ := card_parts_weightPartition_le c hc
        calc macdonaldKernelCoeff q t ⇑r ⇑c = (∏ i, macdonaldG σ q t (r i)).coeff c :=
              (coeff_prod_macdonaldG q t _ c).symm
          _ = (∏ i, macdonaldG σ q t (r i)).coeff (partWeight σ la) :=
              coeff_eq_coeff_partWeight (prod_macdonaldG_isSymmetric q t _) hc
          _ = macdonaldKernelCoeff q t ⇑(partWeight σ la) ⇑r := by
              rw [coeff_prod_macdonaldG, macdonaldKernelCoeff_comm]
          _ = (macdonaldGPart σ q t la).coeff r := by
              rw [macdonaldGPart_eq_prod_partWeight q t la hla, coeff_prod_macdonaldG]
      · rw [ite_eq_right fun h ↦ hr h.1, (isHomogeneous_macdonaldGPart q t _).coeff_eq_zero hr]
    · intro ν _ hne
      rw [TauCeti.coeff_msymm R ν.1 hc, ite_eq_right fun h ↦ hne (Subtype.ext h.symm), mul_zero]
    · exact fun h ↦ absurd (mem_univ _) h
  · rw [ite_eq_right fun h ↦ hc h.2]
    exact (Finset.sum_eq_zero fun ν _ ↦ by
      rw [coeff_msymm_eq_zero_of_degree_ne R ν.1 hc, mul_zero]).symm

end Kernel

section Criterion

variable {d : ℕ}

/-- The kernel `Π_d` is the image of `∑_λ g_λ ⊗ m_λ` under `p ⊗ q ↦ p(x) q(y)`. -/
theorem macdonaldKernelEmbedding_sum (q t : R) :
    macdonaldKernelEmbedding σ R d
        (∑ ν, macdonaldGFamily σ q t d ν ⊗ₜ msymmBasis σ R d ν) =
      macdonaldKernel σ q t d := by
  simp [map_sum, macdonaldKernel_eq_sum]

variable {q t : R} (h : IsUnit ((msymmBasis σ R d).det (macdonaldGFamily σ q t d)))

/-- **Self-adjointness for the `(q, t)` pairing, in the tensor square**: `A` is self-adjoint if
and only if `∑_λ A(g_λ) ⊗ m_λ = ∑_λ g_λ ⊗ A(m_λ)`.  In the basis `g_μ ⊗ m_ν` the two sides have
coordinates `⟨A g_ν, m_μ⟩` and `⟨g_ν, A m_μ⟩`. -/
theorem isSelfAdjoint_macdonaldPairing_iff_sum_tmul
    (A : symmetricHomogeneousSubmodule σ R d →ₗ[R] symmetricHomogeneousSubmodule σ R d) :
    LinearMap.IsSelfAdjoint (macdonaldPairing h) A ↔
      ∑ ν, A (macdonaldGFamily σ q t d ν) ⊗ₜ[R] msymmBasis σ R d ν =
        ∑ ν, macdonaldGFamily σ q t d ν ⊗ₜ[R] A (msymmBasis σ R d ν) := by
  rw [← coe_macdonaldGBasisOfIsUnit h]
  have hl (x : symmetricHomogeneousSubmodule σ R d) (μ) :
      macdonaldPairing h x (msymmBasis σ R d μ) = (macdonaldGBasisOfIsUnit h).repr x μ := by
    rw [macdonaldPairing_apply, Basis.repr_self]
    simp [Finsupp.single_apply]
  have hr (y : symmetricHomogeneousSubmodule σ R d) (ν) :
      macdonaldPairing h (macdonaldGBasisOfIsUnit h ν) y = (msymmBasis σ R d).repr y ν := by
    rw [macdonaldPairing_apply, Basis.repr_self]
    simp [Finsupp.single_apply]
  have key : LinearMap.IsSelfAdjoint (macdonaldPairing h) A ↔
      ∀ μ ν, (macdonaldGBasisOfIsUnit h).repr (A (macdonaldGBasisOfIsUnit h ν)) μ =
        (msymmBasis σ R d).repr (A (msymmBasis σ R d μ)) ν := by
    constructor
    · intro hA μ ν
      rw [← hl, ← hr]
      exact hA _ _
    · intro H
      have hcomp : (macdonaldPairing h).compLeft A = (macdonaldPairing h).compRight A :=
        LinearMap.ext_basis (macdonaldGBasisOfIsUnit h) (msymmBasis σ R d) fun ν μ ↦ by
          rw [LinearMap.BilinForm.compLeft_apply, LinearMap.BilinForm.compRight_apply, hl, hr]
          exact H μ ν
      intro x y
      exact LinearMap.congr_fun₂ hcomp x y
  have hT1 (μ ν) : ((macdonaldGBasisOfIsUnit h).tensorProduct (msymmBasis σ R d)).repr
      (∑ l, A (macdonaldGBasisOfIsUnit h l) ⊗ₜ[R] msymmBasis σ R d l) (μ, ν) =
        (macdonaldGBasisOfIsUnit h).repr (A (macdonaldGBasisOfIsUnit h ν)) μ := by
    simp [-coe_macdonaldGBasisOfIsUnit, Basis.tensorProduct_repr_tmul_apply, Finsupp.single_apply]
  have hT2 (μ ν) : ((macdonaldGBasisOfIsUnit h).tensorProduct (msymmBasis σ R d)).repr
      (∑ l, macdonaldGBasisOfIsUnit h l ⊗ₜ[R] A (msymmBasis σ R d l)) (μ, ν) =
        (msymmBasis σ R d).repr (A (msymmBasis σ R d μ)) ν := by
    simp [-coe_macdonaldGBasisOfIsUnit, Basis.tensorProduct_repr_tmul_apply, Finsupp.single_apply]
  rw [key]
  constructor
  · intro H
    refine ((macdonaldGBasisOfIsUnit h).tensorProduct (msymmBasis σ R d)).repr.injective
      (Finsupp.ext fun ⟨μ, ν⟩ ↦ ?_)
    rw [hT1, hT2, H]
  · intro H μ ν
    rw [← hT1, ← hT2, H]

/-- **The self-adjointness criterion** (Lemma 5 of the Pieri ledger, operator-free part): an
endomorphism `A` of the symmetric polynomials of degree `d` is self-adjoint for the `(q, t)`
pairing if and only if `A` in `x` and `A` in `y` agree on the kernel,
`∑_λ A(g_λ)(x) m_λ(y) = ∑_λ g_λ(x) A(m_λ)(y)`. -/
theorem isSelfAdjoint_macdonaldPairing_iff
    (A : symmetricHomogeneousSubmodule σ R d →ₗ[R] symmetricHomogeneousSubmodule σ R d) :
    LinearMap.IsSelfAdjoint (macdonaldPairing h) A ↔
      ∑ ν, map C (A (macdonaldGFamily σ q t d ν) : MvPolynomial σ R) * C (msymm σ R ν.1) =
        ∑ ν, map C (macdonaldGPart σ q t ν.1) *
          C (A (msymmBasis σ R d ν) : MvPolynomial σ R) := by
  rw [isSelfAdjoint_macdonaldPairing_iff_sum_tmul,
    ← macdonaldKernelEmbedding_inj]
  simp [map_sum]

end Criterion


section Link

/-- There are no contingency tables whose row and column sums have different totals. -/
theorem macdonaldKernelCoeff_eq_zero_of_sum_ne (q t : R) {r c : σ → ℕ}
    (h : ∑ i, r i ≠ ∑ j, c j) : macdonaldKernelCoeff q t r c = 0 := by
  refine Finset.sum_eq_zero fun A hA ↦ absurd ?_ h
  rw [mem_contingencyTables] at hA
  calc ∑ i, r i = ∑ i, ∑ j, A i j := sum_congr rfl fun i _ ↦ (hA.1 i).symm
    _ = ∑ j, ∑ i, A i j := sum_comm
    _ = ∑ j, c j := sum_congr rfl fun j _ ↦ hA.2 j

/-- **`Π_d` is the degree-`d` part of the kernel series**: for `|r| = d`, the coefficient of
`x^r y^c` in `∏_{i,j} f(xᵢ yⱼ)` is the coefficient of `x^r y^c` in
`MvPolynomial.macdonaldKernel`. -/
theorem coeff_macdonaldKernelSeries_eq_coeff_macdonaldKernel (q t : R) {d : ℕ} {r : σ →₀ ℕ}
    (hr : r.degree = d) (c : σ →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.sumElim r c) (macdonaldKernelSeries σ q t) =
      ((macdonaldKernel σ q t d).coeff r).coeff c := by
  rw [coeff_macdonaldKernelSeries, coeff_coeff_macdonaldKernel]
  by_cases hc : c.degree = d
  · rw [ite_eq_left ⟨hr, hc⟩]
  · rw [ite_eq_right fun h ↦ hc h.2, macdonaldKernelCoeff_eq_zero_of_sum_ne]
    rw [← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum, hr]
    exact Ne.symm hc

end Link

end MvPolynomial
