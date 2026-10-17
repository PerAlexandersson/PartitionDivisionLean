/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Macdonald.DiagonalSpecialization
public import PartitionDivision.Macdonald.SchurPrincipal
public import PartitionDivision.Macdonald.Triangular
public import PartitionDivision.TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Symmetric

/-!
# Schur polynomials are eigenvectors of the Macdonald operator at `q = t`

At `q = t` the Macdonald numerator is `Σ_i T_{t, x_i}(a_δ f)`, and the operator
`g ↦ Σ_i T_{t, x_i} g` multiplies the monomial `x^d` by `Σ_i t ^ d_i`.  This weight is invariant
under permuting `d`, so every alternant `a_α` is an eigenvector with eigenvalue `Σ_i t ^ α_i`
(`sum_scaleVar_alternant`).  With the bialternant formula `s_λ a_δ = a_{λ + δ}` this gives
`macdonaldNumerator_schurVec`: the Schur polynomial `s_λ` satisfies the eigenvalue equation of the
first Macdonald operator at `q = t`, with eigenvalue `Σ_i t ^ (λ_i + N - 1 - i)`.

Over `K(t)` these eigenvalues are pairwise distinct (`macdonaldEigenvalue_ratFuncVar_injective`),
because the exponents `λ_i + N - 1 - i` strictly decrease and so determine `λ`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Polynomial

namespace PartitionDivision.Macdonald

open MvPolynomial TauCeti

variable {N : ℕ}

/-- The Schur polynomial of a partition vector is symmetric. -/
theorem schurVec_isSymmetric (K : Type*) [CommSemiring K] (lam : Nat.PartitionVector N) :
    (schurVec K lam).IsSymmetric :=
  isSymmetric_diagramSchurPoly N K _

/-- Scaling one variable multiplies each coefficient by the corresponding power of the scalar. -/
theorem coeff_scaleVar {K : Type*} [CommSemiring K] (c : K) (i : Fin N)
    (f : MvPolynomial (Fin N) K) (d : Fin N →₀ ℕ) :
    (scaleVar c i f).coeff d = c ^ d i * f.coeff d := by
  rw [← scaleVars_singleton, coeff_scaleVars, Finset.prod_singleton]

/-- Every alternant is an eigenvector of `g ↦ Σ_i T_{t, x_i} g`, with eigenvalue `Σ_i t ^ α_i`. -/
theorem sum_scaleVar_alternant {K : Type*} [CommRing K] (t : K) (α : Fin N → ℕ) :
    ∑ i, scaleVar t i (alternant (Fin N) K α) = (∑ i, t ^ α i) • alternant (Fin N) K α := by
  ext d
  rw [coeff_sum, coeff_smul, smul_eq_mul]
  simp_rw [coeff_scaleVar]
  rw [← Finset.sum_mul]
  by_cases h : (alternant (Fin N) K α).coeff d = 0
  · rw [h, mul_zero, mul_zero]
  · obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin N), ⇑d ∘ ⇑τ = α := by
      rw [coeff_alternant] at h
      by_contra hne
      push Not at hne
      apply h
      refine Finset.sum_eq_zero fun τ hτ ↦ ?_
      exact absurd (Finset.mem_filter.mp hτ).2 (hne τ)
    congr 1
    rw [← hτ]
    exact (Equiv.sum_comp τ fun i ↦ t ^ d i).symm

/-- The Vandermonde polynomial is a scalar multiple of the staircase alternant `a_δ`. -/
theorem exists_vandermonde_eq_smul_alternant (K : Type*) [CommRing K] :
    ∃ c : K, vandermonde N K = c • alternant (Fin N) K (fun j ↦ N - 1 - j) := by
  set W : MvPolynomial (Fin N) K := ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (X j - X i)
  set m := ∑ i : Fin N, (Finset.Ioi i).card
  set s : ℤ := (Equiv.Perm.sign (Fin.revPerm (n := N)) : ℤ)
  have hV : vandermonde N K = (-1) ^ m * W := by
    simp only [vandermonde, W, m]
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← Finset.prod_neg]
    exact Finset.prod_congr rfl fun j _ ↦ (neg_sub _ _).symm
  have hA : alternant (Fin N) K (fun j ↦ N - 1 - j) = (s : MvPolynomial (Fin N) K) * W := by
    have hmat : (Matrix.of fun i j : Fin N ↦ (X i : MvPolynomial (Fin N) K) ^ (N - 1 - (j : ℕ))) =
        (Matrix.vandermonde (X : Fin N → MvPolynomial (Fin N) K)).submatrix id Fin.revPerm := by
      ext i j
      simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply,
        Fin.revPerm_apply, Fin.val_rev]
      congr 1
      have := j.isLt
      lia
    rw [alternant_def, hmat, Matrix.det_permute', Matrix.det_vandermonde]
  have hs : s * s = 1 := by simp only [s, ← Units.val_mul, Int.units_mul_self, Units.val_one]
  have hss : (s : MvPolynomial (Fin N) K) * s = 1 := by
    rw [← Int.cast_mul, hs, Int.cast_one]
  refine ⟨(-1) ^ m * (s : K), ?_⟩
  rw [smul_eq_C_mul, map_mul, map_pow, map_neg, map_one, map_intCast, hA, hV,
    show ((-1) ^ m * (s : MvPolynomial (Fin N) K)) * ((s : MvPolynomial (Fin N) K) * W) =
      (-1) ^ m * ((s : MvPolynomial (Fin N) K) * s) * W by ring, hss, mul_one]

/-- The first Macdonald eigenvalue at `q = t` is the power sum of the shifted parts. -/
theorem macdonaldEigenvalue_self {K : Type*} [CommSemiring K] (t : K)
    (lam : Nat.PartitionVector N) :
    macdonaldEigenvalue t t (lam : Fin N → ℕ) = ∑ i : Fin N, t ^ (lam i + (N - 1 - i)) := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← pow_add, Fin.val_rev]
  congr 2
  lia

/-- **Schur polynomials are eigenvectors at `q = t`.**  The Schur polynomial `s_λ` satisfies the
eigenvalue equation of the first Macdonald operator at `q = t`. -/
theorem macdonaldNumerator_schurVec {K : Type*} [CommRing K] (t : K)
    (lam : Nat.PartitionVector N) :
    macdonaldNumerator t t (schurVec K lam) =
      macdonaldEigenvalue t t (lam : Fin N → ℕ) • (vandermonde N K * schurVec K lam) := by
  obtain ⟨c, hc⟩ := exists_vandermonde_eq_smul_alternant (N := N) K
  have hnum : macdonaldNumerator t t (schurVec K lam) =
      ∑ i, scaleVar t i (vandermonde N K * schurVec K lam) := by
    simp only [macdonaldNumerator, map_mul]
  have hVs : vandermonde N K * schurVec K lam =
      c • alternant (Fin N) K (fun j ↦ lam j + (N - 1 - j)) := by
    rw [hc, smul_mul_assoc, mul_comm, schurVec_mul_alternant]
  rw [hnum, hVs]
  simp only [map_smul]
  rw [← Finset.smul_sum, sum_scaleVar_alternant, macdonaldEigenvalue_self, smul_comm]

/-- The shifted parts `λ_i + N - 1 - i` of a partition vector strictly decrease. -/
theorem strictAnti_add_staircase (lam : Nat.PartitionVector N) :
    StrictAnti fun i : Fin N ↦ lam i + (N - 1 - i) := by
  intro i j hij
  have h := lam.antitone hij.le
  have hj := j.isLt
  have hij' : (i : ℕ) < j := hij
  lia

/-- **Distinct eigenvalues at `q = t`.**  Over `K(t)`, the first Macdonald eigenvalues at
`q = t` of distinct partition vectors are distinct. -/
theorem macdonaldEigenvalue_ratFuncVar_injective (K : Type*) [Field K] :
    Function.Injective fun lam : Nat.PartitionVector N ↦
      macdonaldEigenvalue (ratFuncVar K) (ratFuncVar K) (lam : Fin N → ℕ) := by
  intro lam mu h
  have heps (ν : Nat.PartitionVector N) :
      macdonaldEigenvalue (ratFuncVar K) (ratFuncVar K) (ν : Fin N → ℕ) =
        algebraMap K[X] (FractionRing K[X]) (∑ i : Fin N, Polynomial.X ^ (ν i + (N - 1 - i))) := by
    rw [macdonaldEigenvalue_self, map_sum]
    simp [ratFuncVar]
  have hpoly : (∑ i : Fin N, (Polynomial.X : K[X]) ^ (lam i + (N - 1 - i))) =
      ∑ i : Fin N, Polynomial.X ^ (mu i + (N - 1 - i)) :=
    IsFractionRing.injective K[X] (FractionRing K[X]) (by rw [← heps, ← heps]; exact h)
  have hcoeff (ν : Nat.PartitionVector N) (n : ℕ) :
      (∑ i : Fin N, (Polynomial.X : K[X]) ^ (ν i + (N - 1 - i))).coeff n ≠ 0 ↔
        n ∈ Set.range fun i : Fin N ↦ ν i + (N - 1 - i) := by
    classical
    rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_X_pow]
    constructor
    · intro hne
      by_contra hn
      apply hne
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have hni : n ≠ ν i + (N - 1 - i) := fun h ↦ hn ⟨i, h.symm⟩
      simp [hni]
    · rintro ⟨i, rfl⟩
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        have hne : ν i + (N - 1 - i) ≠ ν j + (N - 1 - j) :=
          fun h ↦ hji ((strictAnti_add_staircase ν).injective h).symm
        simp [hne]
      · simp
  have hrange : (Set.range fun i : Fin N ↦ lam i + (N - 1 - i)) =
      Set.range fun i : Fin N ↦ mu i + (N - 1 - i) := by
    ext n
    rw [← hcoeff lam, ← hcoeff mu, hpoly]
  have hfun := ((strictAnti_add_staircase lam).range_inj_of_wellFoundedGT
    (strictAnti_add_staircase mu)).mp hrange
  apply Nat.PartitionVector.ext
  intro i
  have h2 : lam i + (N - 1 - i) = mu i + (N - 1 - i) := congrFun hfun i
  lia

end PartitionDivision.Macdonald
