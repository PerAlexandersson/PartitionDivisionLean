/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Macdonald.BasicLexUnitriangular
public import PartitionDivision.Macdonald.SchurEigen
public import PartitionDivision.Macdonald.Specialization
public import Mathlib.Tactic.LinearCombination

/-!
# Regularity of the Macdonald polynomials at `q = t`, and `u_0(P_λ) ≠ 0`

This file proves Pieri ledger Lemma 8 (`docs/PIERI.md`) without the Pieri rule.

* `coeff_mem_range_of_macdonaldNumerator_eq`: **regularity**.  Let `φ : R →+* F` be a map from a
  domain to a field under which the first Macdonald eigenvalues `ε_μ(φ q, φ t)` are pairwise
  distinct.  A symmetric eigenvector over `Frac R` of the first Macdonald operator at `(q, t)`,
  with eigenvalue `ε_λ` and leading coefficient in the local ring `O` at `ker φ`, has all its
  coefficients in `O`.  Comparing coefficients at `δ + ν` gives a triangular system whose pivots
  `ε_ν - ε_λ` are units of `O`; it is solved by downward induction on `ν`.
* `eq_smul_of_macdonaldNumerator_eq`: when the eigenvalues are pairwise distinct, an eigenvector
  with eigenvalue `ε_λ` is determined by its coefficient at `x^λ`.
* `eval_grid_zero_macdonaldP_ne_zero`: **Lemma 8**, `u_0(P_λ) = P_λ(t^(N-1), …, t, 1) ≠ 0`.  At
  `q = t` the eigenvalues are distinct, so `P_λ` specializes to a multiple of the Schur
  polynomial `s_λ`, whose principal evaluation is nonzero.
-/

@[expose] public section

noncomputable section

open scoped BigOperators MonomialOrder Polynomial

namespace PartitionDivision.Macdonald

open MvPolynomial Nat.PartitionVector

attribute [local instance] RingHom.ker_isPrime

variable {N : ℕ}

/-! ### Coefficient maps -/

section Map

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

/-- Coefficient maps commute with scaling a variable. -/
theorem map_scaleVar (c : R) (i : Fin N) (p : MvPolynomial (Fin N) R) :
    map f (scaleVar c i p) = scaleVar (f c) i (map f p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [← algebraMap_eq, AlgHom.commutes, algebraMap_eq, map_C, ← algebraMap_eq,
        AlgHom.commutes, algebraMap_eq]
  | add p r hp hr => rw [map_add, map_add, hp, hr, map_add, map_add]
  | mul_X p j hp =>
      simp only [map_mul, hp, map_X]
      congr 1
      by_cases hji : j = i
      · subst hji
        simp [smul_eq_C_mul]
      · rw [scaleVar_X_of_ne _ hji, scaleVar_X_of_ne _ hji, map_X]

/-- Coefficient maps preserve the Vandermonde polynomial. -/
theorem map_vandermonde : map f (vandermonde N R) = vandermonde N S := by
  simp [vandermonde, map_prod]

/-- Coefficient maps commute with the Macdonald numerator. -/
theorem map_macdonaldNumerator (q t : R) (p : MvPolynomial (Fin N) R) :
    map f (macdonaldNumerator q t p) = macdonaldNumerator (f q) (f t) (map f p) := by
  simp only [macdonaldNumerator, map_sum, map_mul, map_scaleVar, map_vandermonde]

/-- Ring homomorphisms commute with the first Macdonald eigenvalue. -/
theorem map_macdonaldEigenvalue (q t : R) (lam : Fin N → ℕ) :
    f (macdonaldEigenvalue q t lam) = macdonaldEigenvalue (f q) (f t) lam := by
  simp [macdonaldEigenvalue]

/-- Coefficient maps preserve the monomial symmetric polynomials. -/
theorem map_msymmVec (lam : Nat.PartitionVector N) : map f (msymmVec R lam) = msymmVec S lam := by
  simp [msymmVec, map_sum]

/-- Coefficient maps commute with scalar multiplication. -/
theorem map_smul_eq_smul_map (c : R) (p : MvPolynomial (Fin N) R) :
    map f (c • p) = f c • map f p := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]

end Map

/-! ### Leading coefficients of eigenvectors -/

section Leading

variable {K : Type*} [CommRing K]

/-- The numerator is additive and homogeneous on finite linear combinations. -/
theorem macdonaldNumerator_sum_smul (q t : K) {ι : Type*} (s : Finset ι) (c : ι → K)
    (g : ι → MvPolynomial (Fin N) K) :
    macdonaldNumerator q t (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • macdonaldNumerator q t (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, macdonaldNumerator_add,
        macdonaldNumerator_smul, ih]

/-- Lexicographic comparison of partition vectors through their exponent vectors. -/
theorem lexKey_le_iff (mu lam : Nat.PartitionVector N) :
    lexKey mu ≤ lexKey lam ↔
      toLex (partitionVectorFinsupp mu) ≤ toLex (partitionVectorFinsupp lam) := by
  rw [← not_lt, ← not_lt]
  exact not_congr (lexKey_lt_iff lam mu)

/-- If every partition-vector exponent of a symmetric polynomial with nonzero coefficient is at
most `μ`, then its lexicographic degree is at most `μ`. -/
theorem lex_degree_le_of_isSymmetric {f : MvPolynomial (Fin N) K} (hf : f.IsSymmetric)
    {mu : Nat.PartitionVector N}
    (hmax : ∀ nu : Nat.PartitionVector N, f.coeff (partitionVectorFinsupp nu) ≠ 0 →
      lexKey nu ≤ lexKey mu) :
    MonomialOrder.lex.degree f ≼[MonomialOrder.lex] partitionVectorFinsupp mu := by
  rw [MonomialOrder.degree_le_iff]
  intro b hb
  rw [MonomialOrder.lex_le_iff]
  have hsort : f.coeff (partitionVectorFinsupp (sortDesc b)) ≠ 0 := by
    rw [hf.coeff_sortDesc]
    exact mem_support_iff.mp hb
  exact (toLex_le_partitionVectorFinsupp_of_mem
    (mem_partitionVectorRearrangements_sortDesc b)).trans ((lexKey_le_iff _ _).mp (hmax _ hsort))

variable [IsDomain K]

/-- **The eigenvalue is read off at the leading exponent.**  If a symmetric polynomial satisfies
the numerator equation with eigenvalue `e`, then `e` is the Macdonald eigenvalue of any
lexicographically largest partition vector in its support. -/
theorem eq_macdonaldEigenvalue_of_max (q t e : K) {f : MvPolynomial (Fin N) K}
    (hf : f.IsSymmetric) (heq : macdonaldNumerator q t f = e • (vandermonde N K * f))
    {mu : Nat.PartitionVector N} (hmu : f.coeff (partitionVectorFinsupp mu) ≠ 0)
    (hmax : ∀ nu : Nat.PartitionVector N, f.coeff (partitionVectorFinsupp nu) ≠ 0 →
      lexKey nu ≤ lexKey mu) :
    e = macdonaldEigenvalue q t (mu : Fin N → ℕ) := by
  have hdeg := lex_degree_le_of_isSymmetric hf hmax
  have hc := congrArg (fun p ↦ p.coeff (vandermondeExponent N + partitionVectorFinsupp mu)) heq
  rw [← macdonaldOpNumerator_one, coeff_macdonaldOpNumerator_of_degree_le q t 1 hdeg,
    macdonaldEigenvalueR_one, coeff_smul, smul_eq_mul,
    MonomialOrder.coeff_mul_of_add_of_degree_le (le_of_eq (by rw [lex_degree_vandermonde])) hdeg,
    ← lex_degree_vandermonde (K := K), lex_monic_vandermonde.coeff_degree, one_mul,
    coe_partitionVectorFinsupp] at hc
  exact (mul_right_cancel₀ hmu hc).symm

/-- **Eigenvectors are determined by one coefficient.**  If the first Macdonald eigenvalues are
pairwise distinct, a symmetric eigenvector `f` with eigenvalue `ε_λ` is the multiple
`f_λ • g` of any symmetric eigenvector `g` with the same eigenvalue and `g_λ = 1`. -/
theorem eq_smul_of_macdonaldNumerator_eq (q t : K)
    (hinj : Function.Injective fun lam : Nat.PartitionVector N ↦
      macdonaldEigenvalue q t (lam : Fin N → ℕ))
    {lam : Nat.PartitionVector N} {f g : MvPolynomial (Fin N) K}
    (hf : f.IsSymmetric) (hg : g.IsSymmetric)
    (hfe : macdonaldNumerator q t f =
      macdonaldEigenvalue q t (lam : Fin N → ℕ) • (vandermonde N K * f))
    (hge : macdonaldNumerator q t g =
      macdonaldEigenvalue q t (lam : Fin N → ℕ) • (vandermonde N K * g))
    (hg1 : g.coeff (partitionVectorFinsupp lam) = 1) :
    f = f.coeff (partitionVectorFinsupp lam) • g := by
  set c := f.coeff (partitionVectorFinsupp lam)
  set h := f - c • g with hh
  have hhs : h.IsSymmetric := hf.sub (hg.smul c)
  have hhe : macdonaldNumerator q t h =
      macdonaldEigenvalue q t (lam : Fin N → ℕ) • (vandermonde N K * h) := by
    have hfg : f = h + c • g := by rw [hh, sub_add_cancel]
    have h1 := hfe
    rw [hfg, macdonaldNumerator_add, macdonaldNumerator_smul, hge, mul_add, smul_add,
      mul_smul_comm, smul_comm c] at h1
    exact add_right_cancel h1
  have hlam : h.coeff (partitionVectorFinsupp lam) = 0 := by
    simp [hh, c, hg1]
  rw [← sub_eq_zero]
  refine eq_zero_of_isSymmetric_of_coeff_eq_zero hhs fun mu ↦ ?_
  by_contra hmu
  obtain ⟨nu, hnu, hmax⟩ := exists_lexKey_max_coeff_ne_zero h ⟨mu, hmu⟩
  have he := eq_macdonaldEigenvalue_of_max q t _ hhs hhe hnu hmax
  have hnulam : nu = lam := hinj he.symm
  rw [hnulam] at hnu
  exact hnu hlam

end Leading

/-! ### Regularity -/

section Regularity

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] (φ : R →+* F) (q t : R)

/-- **Regularity of Macdonald eigenvectors.**  Suppose the first Macdonald eigenvalues at
`(φ q, φ t)` are pairwise distinct.  If a symmetric polynomial over `Frac R` satisfies the
numerator equation at `(q, t)` with eigenvalue `ε_λ`, and its coefficient at `x^λ` lies in the
local ring `O` at `ker φ`, then all its coefficients lie in `O`. -/
theorem coeff_mem_range_of_macdonaldNumerator_eq
    (hε : Function.Injective fun lam : Nat.PartitionVector N ↦
      macdonaldEigenvalue (φ q) (φ t) (lam : Fin N → ℕ))
    {f : MvPolynomial (Fin N) (FractionRing R)} (hf : f.IsSymmetric)
    {lam : Nat.PartitionVector N}
    (heq : macdonaldNumerator (algebraMap R (FractionRing R) q) (algebraMap R (FractionRing R) t)
        f = macdonaldEigenvalue (algebraMap R (FractionRing R) q)
          (algebraMap R (FractionRing R) t) (lam : Fin N → ℕ) •
            (vandermonde N (FractionRing R) * f))
    (hlam : f.coeff (partitionVectorFinsupp lam) ∈
      (algebraMap (Localization.AtPrime (RingHom.ker φ)) (FractionRing R)).range)
    (d : Fin N →₀ ℕ) :
    f.coeff d ∈ (algebraMap (Localization.AtPrime (RingHom.ker φ)) (FractionRing R)).range := by
  classical
  set O := Localization.AtPrime (RingHom.ker φ)
  set K := FractionRing R
  set A := (algebraMap O K).range
  set ι := algebraMap R K
  have hA (x : R) : ι x ∈ A := ⟨algebraMap R O x, (IsScalarTower.algebraMap_apply R O K x).symm⟩
  have hinv (x : R) (hx : φ x ≠ 0) : (ι x)⁻¹ ∈ A := by
    let s : (RingHom.ker φ).primeCompl :=
      ⟨x, by rw [Ideal.mem_primeCompl_iff, RingHom.mem_ker]; exact hx⟩
    refine ⟨IsLocalization.mk' O 1 s, ?_⟩
    have hspec := congrArg (algebraMap O K) (IsLocalization.mk'_spec O 1 s)
    rw [map_mul, ← IsScalarTower.algebraMap_apply, map_one, map_one] at hspec
    exact eq_inv_of_mul_eq_one_left hspec
  have hmapA (p : MvPolynomial (Fin N) R) (b : Fin N →₀ ℕ) : (map ι p).coeff b ∈ A := by
    rw [coeff_map]
    exact hA _
  have hNumA (mu : Nat.PartitionVector N) (b : Fin N →₀ ℕ) :
      (macdonaldNumerator (ι q) (ι t) (msymmVec K mu)).coeff b ∈ A := by
    rw [← map_msymmVec ι, ← map_macdonaldNumerator]
    exact hmapA _ b
  have hVA (mu : Nat.PartitionVector N) (b : Fin N →₀ ℕ) :
      (vandermonde N K * msymmVec K mu).coeff b ∈ A := by
    rw [← map_msymmVec ι, ← map_vandermonde ι, ← map_mul]
    exact hmapA _ b
  set eps : Nat.PartitionVector N → K := fun nu ↦ macdonaldEigenvalue (ι q) (ι t) (nu : Fin N → ℕ)
  have hepsA (nu : Nat.PartitionVector N) : eps nu ∈ A := by
    simp only [eps, ← map_macdonaldEigenvalue]
    exact hA _
  set c : Nat.PartitionVector N → K := fun nu ↦ f.coeff (partitionVectorFinsupp nu)
  set S := f.support.image fun b : Fin N →₀ ℕ ↦ sortDesc b
  have hexp : f = ∑ mu ∈ S, c mu • msymmVec K mu := hf.eq_sum_msymmVec
  set D : Nat.PartitionVector N → (Fin N →₀ ℕ) :=
    fun nu ↦ vandermondeExponent N + partitionVectorFinsupp nu
  set e : Nat.PartitionVector N → Nat.PartitionVector N → K := fun nu mu ↦
    (macdonaldNumerator (ι q) (ι t) (msymmVec K mu)).coeff (D nu) -
      eps lam * (vandermonde N K * msymmVec K mu).coeff (D nu)
  have heA (nu mu : Nat.PartitionVector N) : e nu mu ∈ A :=
    A.sub_mem (hNumA mu _) (A.mul_mem (hepsA lam) (hVA mu _))
  -- The coefficient equations.
  have hsys (nu : Nat.PartitionVector N) : ∑ mu ∈ S, c mu * e nu mu = 0 := by
    have h1 := congrArg (fun p ↦ p.coeff (D nu)) heq
    rw [hexp, macdonaldNumerator_sum_smul, Finset.mul_sum, coeff_sum, coeff_smul,
      coeff_sum] at h1
    simp only [coeff_smul, smul_eq_mul, mul_smul_comm] at h1
    rw [Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun mu _ ↦ ?_
    simp only [e, eps]
    ring
  have hdeg (mu : Nat.PartitionVector N) :
      MonomialOrder.lex.degree (msymmVec K mu) ≼[MonomialOrder.lex] partitionVectorFinsupp mu :=
    le_of_eq (by rw [lex_degree_msymmVec])
  have hdiag (nu : Nat.PartitionVector N) : e nu nu = eps nu - eps lam := by
    have h1 : (macdonaldNumerator (ι q) (ι t) (msymmVec K nu)).coeff (D nu) = eps nu := by
      simp only [D]
      rw [← macdonaldOpNumerator_one, coeff_macdonaldOpNumerator_of_degree_le _ _ 1 (hdeg nu),
        macdonaldEigenvalueR_one, coeff_msymmVec_partitionVectorFinsupp,
        coe_partitionVectorFinsupp]
      simp [eps]
    have h2 : (vandermonde N K * msymmVec K nu).coeff (D nu) = 1 := by
      simp only [D]
      rw [MonomialOrder.coeff_mul_of_add_of_degree_le
        (le_of_eq (by rw [lex_degree_vandermonde])) (hdeg nu),
        ← lex_degree_vandermonde (K := K), lex_monic_vandermonde.coeff_degree,
        coeff_msymmVec_partitionVectorFinsupp]
      simp
    simp only [e, h1, h2, mul_one]
  have hbelow (nu mu : Nat.PartitionVector N)
      (hlt : toLex (partitionVectorFinsupp mu) < toLex (partitionVectorFinsupp nu)) :
      e nu mu = 0 := by
    have hlt' : vandermondeExponent N + partitionVectorFinsupp mu ≺[MonomialOrder.lex] D nu := by
      rw [MonomialOrder.lex_lt_iff]
      simp only [D, toLex_add]
      exact (add_lt_add_iff_left _).mpr hlt
    have h1 : (macdonaldNumerator (ι q) (ι t) (msymmVec K mu)).coeff (D nu) = 0 := by
      rw [← macdonaldOpNumerator_one]
      exact MonomialOrder.coeff_eq_zero_of_lt
        ((lex_degree_macdonaldOpNumerator_le _ _ 1 (hdeg mu)).trans_lt hlt')
    have h2 : (vandermonde N K * msymmVec K mu).coeff (D nu) = 0 := by
      refine MonomialOrder.coeff_eq_zero_of_lt (m := MonomialOrder.lex)
        (MonomialOrder.degree_mul_le.trans_lt ?_)
      rw [lex_degree_vandermonde, lex_degree_msymmVec]
      exact hlt'
    simp only [e, h1, h2, mul_zero, sub_zero]
  -- Downward induction on the lexicographic order within `S`.
  set m : Nat.PartitionVector N → ℕ := fun nu ↦
    (S.filter fun mu ↦ toLex (partitionVectorFinsupp nu) < toLex (partitionVectorFinsupp mu)).card
  have hm (nu mu : Nat.PartitionVector N) (hmu : mu ∈ S)
      (hlt : toLex (partitionVectorFinsupp nu) < toLex (partitionVectorFinsupp mu)) :
      m mu < m nu := by
    refine Finset.card_lt_card ⟨fun x hx ↦ ?_, fun hsub ↦ ?_⟩
    · rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, hlt.trans hx.2⟩
    · have := (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hmu, hlt⟩))).2
      exact lt_irrefl _ this
  have hcA (nu : Nat.PartitionVector N) : c nu ∈ A := by
    induction nu using (measure m).wf.induction with
    | _ nu ih =>
    by_cases hc0 : c nu = 0
    · rw [hc0]
      exact A.zero_mem
    by_cases hnl : nu = lam
    · rw [hnl]
      exact hlam
    have hnuS : nu ∈ S := by
      refine Finset.mem_image.mpr ⟨partitionVectorFinsupp nu, mem_support_iff.mpr hc0, ?_⟩
      exact sortDesc_partitionVectorFinsupp nu
    have hrow := hsys nu
    rw [← Finset.add_sum_erase _ _ hnuS, hdiag] at hrow
    have hrest : ∑ mu ∈ S.erase nu, c mu * e nu mu ∈ A := by
      refine A.sum_mem fun mu hmu ↦ ?_
      obtain ⟨hne, hmuS⟩ := Finset.mem_erase.mp hmu
      rcases lt_trichotomy (toLex (partitionVectorFinsupp mu)) (toLex (partitionVectorFinsupp nu))
        with hlt | heq' | hgt
      · rw [hbelow nu mu hlt, mul_zero]
        exact A.zero_mem
      · exact absurd (partitionVectorFinsupp_injective (toLex.injective heq')) hne
      · exact A.mul_mem (ih mu (hm nu mu hmuS hgt)) (heA nu mu)
    set x : R :=
      macdonaldEigenvalue q t (nu : Fin N → ℕ) - macdonaldEigenvalue q t (lam : Fin N → ℕ)
    have hx : φ x ≠ 0 := by
      simp only [x, map_sub, map_macdonaldEigenvalue]
      exact sub_ne_zero.mpr fun h ↦ hnl (hε h)
    have hιx : ι x = eps nu - eps lam := by
      simp only [x, eps, map_sub, map_macdonaldEigenvalue]
    have hxne : ι x ≠ 0 := by
      intro h
      apply hx
      have hx0 : x = 0 := IsFractionRing.injective R K (by rw [h, map_zero])
      rw [hx0, map_zero]
    have hcnu : c nu = (-∑ mu ∈ S.erase nu, c mu * e nu mu) * (ι x)⁻¹ := by
      rw [hιx] at hxne ⊢
      rw [eq_mul_inv_iff_mul_eq₀ hxne]
      linear_combination hrow
    rw [hcnu]
    exact A.mul_mem (A.neg_mem hrest) (hinv x hx)
  rw [← hf.coeff_sortDesc d]
  exact hcA _

end Regularity

/-! ### Lemma 8 -/

/-- `ℚ(q, t)`, the field of the generic Macdonald polynomials. -/
local notation "𝕂" => FractionRing (MvPolynomial (Fin 2) ℚ)

/-- The local ring of `ℚ[q, t]` at the kernel of the diagonal specialization `q = t`. -/
abbrev DiagonalLocalRing : Type :=
  Localization.AtPrime (RingHom.ker diagonalSpecialization)

/-- At `q = t` the first Macdonald eigenvalues are pairwise distinct. -/
theorem macdonaldEigenvalue_diagonalSpecialization_injective :
    Function.Injective fun lam : Nat.PartitionVector N ↦
      macdonaldEigenvalue (diagonalSpecialization (X 0)) (diagonalSpecialization (X 1))
        (lam : Fin N → ℕ) := by
  simp only [diagonalSpecialization_X_zero, diagonalSpecialization_X_one]
  exact macdonaldEigenvalue_ratFuncVar_injective ℚ

/-- **Regularity of `P_λ` at `q = t`.**  Every coefficient of the Macdonald polynomial lies in the
local ring at `q = t`. -/
theorem macdonaldP_mem_range_map_diagonal (lam : Nat.PartitionVector N) :
    macdonaldP lam ∈ Set.range (map (algebraMap DiagonalLocalRing 𝕂)) := by
  rw [mem_range_map_iff_coeffs_subset]
  intro a ha
  obtain ⟨b, -, rfl⟩ := mem_coeffs_iff.mp ha
  refine coeff_mem_range_of_macdonaldNumerator_eq diagonalSpecialization (X 0) (X 1)
    macdonaldEigenvalue_diagonalSpecialization_injective (macdonaldP_isSymmetric lam)
    (macdonaldNumerator_macdonaldP lam) ?_ b
  rw [(isLexUnitriangular_macdonaldP lam).coeff_self]
  exact Subring.one_mem _

/-- The coefficientwise preimage of `P_λ` in the local ring at `q = t`. -/
def macdonaldPDiagonalLift (lam : Nat.PartitionVector N) :
    MvPolynomial (Fin N) DiagonalLocalRing :=
  (macdonaldP_mem_range_map_diagonal lam).choose

/-- The preimage maps back to `P_λ`. -/
theorem map_macdonaldPDiagonalLift (lam : Nat.PartitionVector N) :
    map (algebraMap DiagonalLocalRing 𝕂) (macdonaldPDiagonalLift lam) = macdonaldP lam :=
  (macdonaldP_mem_range_map_diagonal lam).choose_spec

/-- The specialization `P_λ(x; t, t)` of the Macdonald polynomial at `q = t`, over `ℚ(t)`. -/
def macdonaldPDiagonal (lam : Nat.PartitionVector N) : MvPolynomial (Fin N) (FractionRing ℚ[X]) :=
  map (specializationHom diagonalSpecialization) (macdonaldPDiagonalLift lam)

/-- The specialization at `q = t` is lex-unitriangular. -/
theorem isLexUnitriangular_macdonaldPDiagonal (lam : Nat.PartitionVector N) :
    IsLexUnitriangular (macdonaldPDiagonal lam) lam :=
  (IsLexUnitriangular.of_map (algebraMap_localization_fractionRing_injective _)
    (by rw [map_macdonaldPDiagonalLift]; exact isLexUnitriangular_macdonaldP lam)).map _

/-- The specialization at `q = t` satisfies the eigenvalue equation of the first Macdonald
operator at `q = t`. -/
theorem macdonaldNumerator_macdonaldPDiagonal (lam : Nat.PartitionVector N) :
    macdonaldNumerator (ratFuncVar ℚ) (ratFuncVar ℚ) (macdonaldPDiagonal lam) =
      macdonaldEigenvalue (ratFuncVar ℚ) (ratFuncVar ℚ) (lam : Fin N → ℕ) •
        (vandermonde N (FractionRing ℚ[X]) * macdonaldPDiagonal lam) := by
  set ι := algebraMap DiagonalLocalRing 𝕂
  set σ := specializationHom diagonalSpecialization
  set qO := algebraMap (MvPolynomial (Fin 2) ℚ) DiagonalLocalRing (X 0)
  set tO := algebraMap (MvPolynomial (Fin 2) ℚ) DiagonalLocalRing (X 1)
  have hq : ι qO = macdonaldParamQ := (IsScalarTower.algebraMap_apply _ _ _ _).symm
  have ht : ι tO = macdonaldParamT := (IsScalarTower.algebraMap_apply _ _ _ _).symm
  have hO : macdonaldNumerator qO tO (macdonaldPDiagonalLift lam) =
      macdonaldEigenvalue qO tO (lam : Fin N → ℕ) •
        (vandermonde N DiagonalLocalRing * macdonaldPDiagonalLift lam) := by
    apply map_injective _ (algebraMap_localization_fractionRing_injective diagonalSpecialization)
    rw [map_macdonaldNumerator, map_smul_eq_smul_map, map_mul, map_vandermonde,
      map_macdonaldEigenvalue,
      map_macdonaldPDiagonalLift, hq, ht]
    exact macdonaldNumerator_macdonaldP lam
  have hσq : σ qO = ratFuncVar ℚ := by
    rw [specializationHom_algebraMap, diagonalSpecialization_X_zero]
  have hσt : σ tO = ratFuncVar ℚ := by
    rw [specializationHom_algebraMap, diagonalSpecialization_X_one]
  have h := congrArg (map σ) hO
  rw [map_macdonaldNumerator, map_smul_eq_smul_map, map_mul, map_vandermonde,
    map_macdonaldEigenvalue,
    hσq, hσt] at h
  exact h

/-- **At `q = t` the Macdonald polynomial specializes to a multiple of the Schur polynomial**:
`s_λ = c • P_λ(x; t, t)` with `c` the coefficient of `x^λ` in `s_λ`. -/
theorem schurVec_eq_smul_macdonaldPDiagonal (lam : Nat.PartitionVector N) :
    schurVec (FractionRing ℚ[X]) lam =
      (schurVec (FractionRing ℚ[X]) lam).coeff (partitionVectorFinsupp lam) •
        macdonaldPDiagonal lam :=
  eq_smul_of_macdonaldNumerator_eq (ratFuncVar ℚ) (ratFuncVar ℚ)
    (macdonaldEigenvalue_ratFuncVar_injective ℚ)
    (schurVec_isSymmetric _ lam) (isLexUnitriangular_macdonaldPDiagonal lam).isSymmetric
    (macdonaldNumerator_schurVec _ lam) (macdonaldNumerator_macdonaldPDiagonal lam)
    (isLexUnitriangular_macdonaldPDiagonal lam).coeff_self

/-- **Pieri ledger Lemma 8: `u_0(P_λ) ≠ 0`.**  The Macdonald polynomial evaluated at the point
`x_i = t ^ (N - 1 - i)` is nonzero in `ℚ(q, t)`.  No Pieri rule is used. -/
theorem eval_grid_zero_macdonaldP_ne_zero (lam : Nat.PartitionVector N) :
    eval (grid macdonaldParamQ macdonaldParamT 0) (macdonaldP lam) ≠ 0 := by
  set ι := algebraMap DiagonalLocalRing 𝕂
  set σ := specializationHom diagonalSpecialization
  set y : Fin N → DiagonalLocalRing := fun i ↦
    algebraMap (MvPolynomial (Fin 2) ℚ) DiagonalLocalRing (X 1) ^ (N - 1 - (i : ℕ))
  have hgrid : grid macdonaldParamQ macdonaldParamT (0 : Nat.PartitionVector N) = ι ∘ y := by
    funext i
    simp [grid, staircase, y, ι, ← IsScalarTower.algebraMap_apply]
  have hK : eval (grid macdonaldParamQ macdonaldParamT 0) (macdonaldP lam) =
      ι (eval y (macdonaldPDiagonalLift lam)) := by
    rw [eval₂_comp, ← eval_map, map_macdonaldPDiagonalLift, hgrid]
  have hσy : σ ∘ y = fun i : Fin N ↦ ratFuncVar ℚ ^ (N - 1 - (i : ℕ)) := by
    funext i
    simp only [Function.comp_apply, map_pow, y, σ]
    rw [specializationHom_algebraMap, diagonalSpecialization_X_one]
  have hF : σ (eval y (macdonaldPDiagonalLift lam)) =
      eval (fun i : Fin N ↦ ratFuncVar ℚ ^ (N - 1 - (i : ℕ))) (macdonaldPDiagonal lam) := by
    rw [eval₂_comp, ← eval_map, hσy]
    rfl
  have hschur := eval_schurVec_ne_zero (injective_pow_ratFuncVar ℚ) (N := N) lam
  rw [schurVec_eq_smul_macdonaldPDiagonal, smul_eval] at hschur
  have hP := right_ne_zero_of_mul hschur
  rw [hK]
  intro h0
  apply hP
  rw [← hF, (algebraMap_localization_fractionRing_injective _) (h0.trans (map_zero ι).symm),
    map_zero]

end PartitionDivision.Macdonald
