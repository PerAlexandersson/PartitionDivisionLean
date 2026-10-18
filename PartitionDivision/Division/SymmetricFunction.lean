/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import PartitionDivision.Division.Main
public import PartitionDivision.Mathlib.RingTheory.MvPolynomial.ExponentFilter
public import PartitionDivision.Mathlib.RingTheory.MvPolynomial.Symmetric.ElementaryExpansion

/-!
# The partition-division theorem for symmetric functions

We state and prove the partition-division theorem in countably many variables, in the model of
multivariate power series `MvPowerSeries ℕ R`, without constructing the ring `Λ` of symmetric
functions.

* `esymmSeries σ R r` is `e_r = Σ_{|S| = r} x^S`, and `esymmSeriesPart σ R μ` is `e_μ`.
* `msymmSeries σ R λ` is the monomial symmetric function `m_λ`: the sum of all monomials whose
  nonzero exponents form the multiset of parts of `λ`.
* `partitionDivision σ R k` is the operator `R_k`, with `coeff d (R_k f) = coeff (k • d) f`.

`partitionDivision_msymmSeries` and `partitionDivision_msymmSeries_eq_zero` show that
`partitionDivision` is the operator `R_k` of the paper: `R_k m_λ = m_{λ/k}` when `k` divides
every part of `λ`, and `R_k m_λ = 0` otherwise.

The main theorem `partitionDivision_ePositive` says that for `0 < k` and
`μ ⊢ k n`, `R_k(e_μ)` is a natural-number combination of the `e_ν`, `ν ⊢ n`.

**Remark.**  The symmetric functions over `ℤ` are the symmetric power series of bounded degree
in `MvPowerSeries ℕ ℤ`.  The `e_μ` and `m_λ` above are such series, so the main theorem is the
statement `R_k(e_μ) ∈ ℕ{e_ν}` in `Λ`.

The proof restricts to finitely many variables with `MvPowerSeries.killCompl` and applies the
finite theorem `exponentDiv_esymmPart_ePositive`.  The coefficients do not
depend on the number of variables, by linear independence of the `e_ν` in `n` variables.
-/

@[expose] public section

noncomputable section

open Finset

namespace PartitionDivision

variable {σ τ : Type*}

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

/-- The operator `R_k` on power series: `coeff d (R_k f) = coeff (k • d) f`. -/
def partitionDivision (k : ℕ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun f := fun d ↦ f (k • d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Definitions

variable {R : Type*} [CommSemiring R]

open Classical in
theorem coeff_esymmSeries (r : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (esymmSeries σ R r) =
      if (∀ i, d i ≤ 1) ∧ d.degree = r then 1 else 0 := by
  classical
  rw [MvPowerSeries.coeff_apply]
  unfold esymmSeries
  by_cases h : (∀ i, d i ≤ 1) ∧ d.degree = r <;> simp [h]

theorem coeff_msymmSeries {n : ℕ} (lam : n.Partition) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (msymmSeries σ R lam) =
      if d.support.val.map d = lam.parts then 1 else 0 :=
  MvPowerSeries.coeff_apply _ _

@[simp]
theorem coeff_partitionDivision (k : ℕ) (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (partitionDivision σ R k f) = MvPowerSeries.coeff (k • d) f := by
  rw [MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply]
  rfl

/-! ### `partitionDivision` is `R_k` -/

/-- The nonzero exponents of `k • d` are those of `d`, multiplied by `k`. -/
private theorem values_smul {k : ℕ} (hk : 0 < k) (d : σ →₀ ℕ) :
    (k • d).support.val.map (k • d) = (d.support.val.map d).map (k * ·) := by
  rw [Finsupp.support_smul_eq hk.ne', Multiset.map_map]
  rfl

/-- If `λ = k ν`, then `R_k m_λ = m_ν`. -/
theorem partitionDivision_msymmSeries {k m n : ℕ} (hk : 0 < k) (lam : n.Partition)
    (nu : m.Partition) (h : lam.parts = nu.parts.map (k * ·)) :
    partitionDivision σ R k (msymmSeries σ R lam) = msymmSeries σ R nu := by
  have hinj : Function.Injective (fun a : ℕ ↦ k * a) :=
    fun a b hab ↦ Nat.eq_of_mul_eq_mul_left hk hab
  ext d
  simp only [coeff_partitionDivision, coeff_msymmSeries, values_smul hk, h,
    (Multiset.map_injective hinj).eq_iff]

/-- If some part of `λ` is not divisible by `k`, then `R_k m_λ = 0`. -/
theorem partitionDivision_msymmSeries_eq_zero {k n : ℕ} (hk : 0 < k) (lam : n.Partition)
    (h : ∃ p ∈ lam.parts, ¬ k ∣ p) :
    partitionDivision σ R k (msymmSeries σ R lam) = 0 := by
  ext d
  rw [coeff_partitionDivision, coeff_msymmSeries, values_smul hk, map_zero, ite_eq_right_iff]
  intro heq
  exfalso
  obtain ⟨p, hp, hndvd⟩ := h
  rw [← heq, Multiset.mem_map] at hp
  obtain ⟨a, _, rfl⟩ := hp
  exact hndvd (dvd_mul_right k a)

/-! ### Elementary symmetric polynomials as series -/

/-- The indicator exponent of a finite set. -/
private theorem sum_single_apply [DecidableEq σ] (t : Finset σ) (j : σ) :
    (∑ i ∈ t, Finsupp.single i 1 : σ →₀ ℕ) j = if j ∈ t then 1 else 0 := by
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

private theorem degree_sum_single (t : Finset σ) :
    (∑ i ∈ t, Finsupp.single i 1 : σ →₀ ℕ).degree = t.card := by
  rw [map_sum]
  simp

private theorem sum_single_injective :
    Function.Injective fun t : Finset σ ↦ (∑ i ∈ t, Finsupp.single i 1 : σ →₀ ℕ) := by
  classical
  intro s t h
  ext j
  have hj := congrArg (fun d : σ →₀ ℕ ↦ d j) h
  simp only [sum_single_apply] at hj
  by_cases hs : j ∈ s <;> by_cases ht : j ∈ t <;> simp_all

/-- A squarefree exponent is the indicator of its support. -/
private theorem sum_single_support {d : σ →₀ ℕ} (hd : ∀ i, d i ≤ 1) :
    (∑ i ∈ d.support, Finsupp.single i 1 : σ →₀ ℕ) = d := by
  classical
  ext j
  rw [sum_single_apply]
  by_cases hj : j ∈ d.support
  · simp only [hj, ↓reduceIte]
    have := hd j
    rw [Finsupp.mem_support_iff] at hj
    lia
  · simp only [hj, ↓reduceIte]
    exact (Finsupp.notMem_support_iff.mp hj).symm

open Classical in
/-- The coefficients of the elementary symmetric polynomial. -/
theorem coeff_esymm_eq_ite [Fintype σ] (r : ℕ) (d : σ →₀ ℕ) :
    (MvPolynomial.esymm σ R r).coeff d =
      if (∀ i, d i ≤ 1) ∧ d.degree = r then 1 else 0 := by
  classical
  rw [MvPolynomial.esymm_eq_sum_monomial, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · have hmem : d.support ∈ (Finset.univ : Finset σ).powersetCard r := by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [← degree_sum_single, sum_single_support h.1, h.2]
    rw [Finset.sum_eq_single d.support]
    · simp only [sum_single_support h.1, ↓reduceIte]
    · intro t _ ht
      rw [ite_eq_right_iff]
      intro heq
      exfalso
      apply ht
      apply sum_single_injective
      change (∑ i ∈ t, Finsupp.single i 1 : σ →₀ ℕ) = ∑ i ∈ d.support, Finsupp.single i 1
      rw [heq, sum_single_support h.1]
    · intro h'
      exact absurd hmem h'
  · apply Finset.sum_eq_zero
    intro t ht
    rw [ite_eq_right_iff]
    rintro rfl
    exfalso
    apply h
    refine ⟨fun i ↦ ?_, ?_⟩
    · rw [sum_single_apply]
      split_ifs <;> lia
    · rw [degree_sum_single]
      exact (Finset.mem_powersetCard.mp ht).2

/-- In finitely many variables, `e_r` is the elementary symmetric polynomial. -/
theorem coe_esymm [Fintype σ] (r : ℕ) :
    (MvPolynomial.esymm σ R r : MvPowerSeries σ R) = esymmSeries σ R r := by
  classical
  ext d
  rw [MvPolynomial.coeff_coe, coeff_esymm_eq_ite, coeff_esymmSeries]
  split_ifs <;> rfl

/-- In finitely many variables, `e_μ` is the elementary symmetric polynomial `esymmPart μ`. -/
theorem coe_esymmPart [Fintype σ] {n : ℕ} (mu : n.Partition) :
    (MvPolynomial.esymmPart σ R mu : MvPowerSeries σ R) = esymmSeriesPart σ R mu := by
  rw [MvPolynomial.esymmPart, esymmSeriesPart,
    ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro r _
  exact coe_esymm r

/-! ### Exponent division as `R_k` -/

/-- Coefficients of `exponentDiv k`, for `0 < k`. -/
theorem coeff_exponentDiv {k : ℕ} (hk : 0 < k) (p : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (MvPolynomial.exponentDiv k p).coeff d = p.coeff (k • d) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e r =>
      rw [MvPolynomial.exponentDiv_monomial, MvPolynomial.coeff_monomial]
      by_cases he : MvPolynomial.ExponentsDivisibleBy k e
      · simp only [he, ↓reduceIte]
        rw [MvPolynomial.coeff_monomial]
        have hiff : MvPolynomial.exponentQuotient k e = d ↔ e = k • d := by
          constructor
          · rintro rfl
            ext i
            simp [Nat.mul_div_cancel' (he i)]
          · rintro rfl
            ext i
            simp [hk.ne']
        by_cases hd : e = k • d
        · simp only [hiff.mpr hd, ↓reduceIte]
          simp only [hd, ↓reduceIte]
        · have hd' : MvPolynomial.exponentQuotient k e ≠ d := fun h ↦ hd (hiff.mp h)
          simp only [hd', hd, ↓reduceIte]
      · have hne : e ≠ k • d := by
          rintro rfl
          exact he fun i ↦ by simp
        simp [he, hne]
  | add p q hp hq => simp [hp, hq]

/-- Exponent division of a polynomial is `R_k` of its power series. -/
theorem coe_exponentDiv {k : ℕ} (hk : 0 < k) (p : MvPolynomial σ R) :
    (MvPolynomial.exponentDiv k p : MvPowerSeries σ R) = partitionDivision σ R k p := by
  ext d
  rw [MvPolynomial.coeff_coe, coeff_exponentDiv hk, coeff_partitionDivision, MvPolynomial.coeff_coe]

/-- The power series of a finite linear combination of polynomials. -/
theorem coe_sum_smul {ι : Type*} (s : Finset ι) (a : ι → R) (p : ι → MvPolynomial σ R) :
    ((∑ i ∈ s, a i • p i : MvPolynomial σ R) : MvPowerSeries σ R) =
      ∑ i ∈ s, a i • (p i : MvPowerSeries σ R) := by
  ext d
  simp [map_sum]

/-! ### Restriction to finitely many variables -/

private theorem embDomain_smul (e : σ ↪ τ) (k : ℕ) (x : σ →₀ ℕ) :
    Finsupp.embDomain e (k • x) = k • Finsupp.embDomain e x := by
  ext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simp
  · rw [Finsupp.embDomain_of_notMem_range _ _ _ hj, Finsupp.smul_apply,
      Finsupp.embDomain_of_notMem_range _ _ _ hj, smul_zero]

private theorem degree_embDomain (e : σ ↪ τ) (x : σ →₀ ℕ) :
    (Finsupp.embDomain e x).degree = x.degree := by
  rw [Finsupp.degree_apply, Finsupp.degree_apply, Finsupp.support_embDomain, Finset.sum_map]
  simp

/-- Restriction is linear. -/
private theorem killCompl_sum_smul (e : σ ↪ τ) {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (f : ι → MvPowerSeries τ ℤ) :
    MvPowerSeries.killCompl e (∑ i ∈ s, a i • f i) =
      ∑ i ∈ s, a i • MvPowerSeries.killCompl e (f i) := by
  ext x
  simp [map_sum]

/-- Restriction sends `e_r` to `e_r`. -/
theorem killCompl_esymmSeries (e : σ ↪ τ) (r : ℕ) :
    MvPowerSeries.killCompl e (esymmSeries τ R r) = esymmSeries σ R r := by
  ext x
  rw [MvPowerSeries.coeff_killCompl, coeff_esymmSeries, coeff_esymmSeries, degree_embDomain]
  have hsq : (∀ j, Finsupp.embDomain e x j ≤ 1) ↔ ∀ i, x i ≤ 1 := by
    constructor
    · intro h i
      simpa using h (e i)
    · intro h j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        simpa using h i
      · rw [Finsupp.embDomain_of_notMem_range _ _ _ hj]
        exact Nat.zero_le _
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd ⟨hsq.mp h1.1, h1.2⟩ h2
  · exact absurd ⟨hsq.mpr h3.1, h3.2⟩ h1
  · rfl

/-- Restriction sends `e_μ` to `e_μ`. -/
theorem killCompl_esymmSeriesPart (e : σ ↪ τ) {n : ℕ} (mu : n.Partition) :
    MvPowerSeries.killCompl e (esymmSeriesPart τ R mu) = esymmSeriesPart σ R mu := by
  rw [esymmSeriesPart, esymmSeriesPart, map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro r _
  exact killCompl_esymmSeries e r

/-- Restriction commutes with `R_k`. -/
theorem killCompl_partitionDivision (e : σ ↪ τ) (k : ℕ) (f : MvPowerSeries τ R) :
    MvPowerSeries.killCompl e (partitionDivision τ R k f) =
      partitionDivision σ R k (MvPowerSeries.killCompl e f) := by
  ext x
  rw [MvPowerSeries.coeff_killCompl, coeff_partitionDivision, coeff_partitionDivision,
    MvPowerSeries.coeff_killCompl, embDomain_smul]

/-! ### The main theorem -/

/-- The finite theorem in `N ≥ n` variables, written with power series and integer
coefficients. -/
private theorem exists_int_series_expansion {k n N : ℕ} (hk : 0 < k) (hn : n ≤ N)
    (mu : (k * n).Partition) :
    ∃ c : n.Partition → ℕ,
      partitionDivision (Fin N) ℤ k (esymmSeriesPart (Fin N) ℤ mu) =
        ∑ nu, (c nu : ℤ) • esymmSeriesPart (Fin N) ℤ nu := by
  obtain ⟨c, hc⟩ := exponentDiv_esymmPart_ePositive hk hn mu
  refine ⟨c, ?_⟩
  have h : ((MvPolynomial.exponentDiv k (MvPolynomial.esymmPart (Fin N) ℤ mu) :
      MvPolynomial (Fin N) ℤ) : MvPowerSeries (Fin N) ℤ) =
      ((∑ nu, c nu • MvPolynomial.esymmPart (Fin N) ℤ nu : MvPolynomial (Fin N) ℤ) :
        MvPowerSeries (Fin N) ℤ) := by
    rw [hc]
  rw [coe_exponentDiv hk, coe_esymmPart] at h
  rw [h]
  simp_rw [← Nat.cast_smul_eq_nsmul ℤ]
  rw [coe_sum_smul]
  simp_rw [coe_esymmPart]
  rfl

/-- The expansion coefficients in `N ≥ n` variables are those in `n` variables. -/
private theorem series_expansion_of_le {k n N : ℕ} (hk : 0 < k) (hn : n ≤ N)
    (mu : (k * n).Partition) (c : n.Partition → ℕ)
    (hc : partitionDivision (Fin n) ℤ k (esymmSeriesPart (Fin n) ℤ mu) =
      ∑ nu, (c nu : ℤ) • esymmSeriesPart (Fin n) ℤ nu) :
    partitionDivision (Fin N) ℤ k (esymmSeriesPart (Fin N) ℤ mu) =
      ∑ nu, (c nu : ℤ) • esymmSeriesPart (Fin N) ℤ nu := by
  obtain ⟨b, hb⟩ := exists_int_series_expansion (N := N) hk hn mu
  have hres := congrArg (MvPowerSeries.killCompl (R := ℤ) (Fin.castLEEmb hn)) hb
  rw [killCompl_partitionDivision, killCompl_esymmSeriesPart, killCompl_sum_smul, hc] at hres
  simp only [killCompl_esymmSeriesPart] at hres
  have hseries0 : ∑ nu, ((b nu : ℤ) - c nu) • esymmSeriesPart (Fin n) ℤ nu = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, ← hres, sub_self]
  have hpoly : ∑ nu, ((b nu : ℤ) - c nu) • MvPolynomial.esymmPart (Fin n) ℤ nu = 0 := by
    apply MvPolynomial.coe_injective
    rw [coe_sum_smul, MvPolynomial.coe_zero]
    simp_rw [coe_esymmPart]
    exact hseries0
  have hbc : ∀ nu, b nu = c nu := by
    intro nu
    have h := Fintype.linearIndependent_iff.mp (MvPolynomial.linearIndependent_esymmPart
      (R := ℤ) (le_refl n)) _ hpoly nu
    exact_mod_cast sub_eq_zero.mp h
  rw [hb]
  simp_rw [hbc]

/-- **The partition-division theorem for symmetric functions.**  For `0 < k` and `μ ⊢ k n`,
`R_k(e_μ)` is a natural-number combination of the `e_ν`, `ν ⊢ n`, in countably many
variables. -/
theorem partitionDivision_ePositive {k n : ℕ} (hk : 0 < k)
    (mu : (k * n).Partition) :
    ∃ c : n.Partition → ℕ,
      partitionDivision ℕ ℤ k (esymmSeriesPart ℕ ℤ mu) =
        ∑ nu, (c nu : ℤ) • esymmSeriesPart ℕ ℤ nu := by
  obtain ⟨c, hc⟩ := exists_int_series_expansion (N := n) hk le_rfl mu
  refine ⟨c, ?_⟩
  ext d
  obtain ⟨N, hnN, hsupp⟩ : ∃ N, n ≤ N ∧ ∀ i ∈ d.support, i < N := by
    refine ⟨n + d.support.sup id + 1, by lia, fun i hi ↦ ?_⟩
    have := Finset.le_sup (f := id) hi
    simp only [id] at this
    lia
  have hd : d ∈ Set.range (Finsupp.embDomain (Fin.valEmbedding (n := N))) := by
    rw [Finsupp.mem_range_embDomain_iff]
    intro i hi
    exact ⟨⟨i, hsupp i (Finset.mem_coe.mp hi)⟩, rfl⟩
  obtain ⟨x, rfl⟩ := hd
  have hseries := series_expansion_of_le hk hnN mu c hc
  rw [← MvPowerSeries.coeff_killCompl, ← MvPowerSeries.coeff_killCompl,
    killCompl_partitionDivision, killCompl_esymmSeriesPart, hseries, killCompl_sum_smul]
  simp only [killCompl_esymmSeriesPart]

end PartitionDivision
