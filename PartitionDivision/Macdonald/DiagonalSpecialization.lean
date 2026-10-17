/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Macdonald.PieriCoefficient
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The diagonal specialization `q = t`

At `q = t` the row-pair factors of the vertical Pieri coefficient cancel: for a legal strip,
numerator and denominator are the same product (`pieriNum_self_eq_pieriDen`), because
`1 - q^a t^b` only depends on `a + b` when `q = t`.  Every denominator factor becomes
`1 - t ^ n` with `n ≥ 1`, so it survives whenever no positive power of `t` is one
(`pieriDen_self_ne_zero`).

`diagonalSpecialization : ℚ[q, t] →+* ℚ(t)` is the map `q, t ↦ t`.  The Pieri denominators survive
it (`pieriDen_diagonalSpecialization_ne_zero`), so it is a valid specialization for the machinery
of `PartitionDivision.Macdonald.Specialization`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Polynomial

namespace PartitionDivision.Macdonald

open Nat.PartitionVector.Pieri

variable {N : ℕ}

/-- At `q = t` the basic binomial `1 - q ^ a t ^ b` is `1 - t ^ (a + b)`. -/
theorem binomial_self {R : Type*} [CommRing R] (t : R) (a b : ℕ) :
    binomial t t a b = 1 - t ^ (a + b) := by
  rw [binomial, pow_add]

/-- At `q = t` the numerator and denominator of a contributing row pair of a legal strip agree. -/
theorem pairNum_self_eq_pairDen {R : Type*} [CommRing R] (t : R)
    {lam : Nat.PartitionVector N} {δ : Strip N} (hδ : IsLegal lam δ)
    {ij : Fin N × Fin N} (hij : ij ∈ rowPairs δ) :
    pairNum lam t t ij = pairDen lam t t ij := by
  have hd := rowDifference_pos hδ hij
  have hm := rowDistance_pos hij
  rw [pairNum, pairDen, binomial_self, binomial_self, binomial_self, binomial_self, mul_comm]
  congr 3 <;> lia

/-- **`ψ'(t, t) = 1`.**  At `q = t` the Pieri numerator of a legal strip equals its
denominator. -/
theorem pieriNum_self_eq_pieriDen {R : Type*} [CommRing R] (t : R)
    {lam : Nat.PartitionVector N} {δ : Strip N} (hδ : IsLegal lam δ) :
    pieriNum lam δ t t = pieriDen lam δ t t :=
  Finset.prod_congr rfl fun _ hij ↦ pairNum_self_eq_pairDen t hδ hij

/-- At `q = t` every Pieri denominator is nonzero if no positive power of `t` is one.  No
legality is needed: every factor is `1 - t ^ n` with `n` at least the positive row distance. -/
theorem pieriDen_self_ne_zero {R : Type*} [CommRing R] [IsDomain R] {t : R}
    (ht : ∀ n : ℕ, n ≠ 0 → t ^ n ≠ 1) (lam : Nat.PartitionVector N) (δ : Strip N) :
    pieriDen lam δ t t ≠ 0 := by
  rw [pieriDen, Finset.prod_ne_zero_iff]
  intro ij hij
  have hm := rowDistance_pos hij
  rw [pairDen, binomial_self, binomial_self]
  refine mul_ne_zero ?_ ?_ <;> rw [sub_ne_zero] <;> refine fun h ↦ ht _ ?_ h.symm <;> lia

section Diagonal

variable (K : Type*) [Field K]

/-- The image of the variable in the rational function field `K(t) = FractionRing K[X]`. -/
abbrev ratFuncVar : FractionRing K[X] := algebraMap K[X] (FractionRing K[X]) Polynomial.X

/-- The powers of the variable of `K(t)` are pairwise distinct. -/
theorem injective_pow_ratFuncVar : Function.Injective fun n : ℕ ↦ ratFuncVar K ^ n := by
  intro a b h
  simp only [ratFuncVar, ← map_pow] at h
  have h' := congrArg Polynomial.natDegree (IsFractionRing.injective K[X] (FractionRing K[X]) h)
  simpa using h'

/-- No positive power of the variable of `K(t)` is one. -/
theorem ratFuncVar_pow_ne_one {n : ℕ} (hn : n ≠ 0) : ratFuncVar K ^ n ≠ 1 := by
  intro h
  apply hn
  apply injective_pow_ratFuncVar K
  simpa using h

/-- The diagonal specialization `q ↦ t`, `t ↦ t` from `ℚ[q, t]` to `ℚ(t)`. -/
def diagonalSpecialization : MvPolynomial (Fin 2) ℚ →+* FractionRing ℚ[X] :=
  MvPolynomial.eval₂Hom ((algebraMap ℚ[X] (FractionRing ℚ[X])).comp Polynomial.C)
    ![ratFuncVar ℚ, ratFuncVar ℚ]

/-- The diagonal specialization sends `q` to `t`. -/
@[simp]
theorem diagonalSpecialization_X_zero :
    diagonalSpecialization (MvPolynomial.X 0) = ratFuncVar ℚ := by
  simp [diagonalSpecialization]

/-- The diagonal specialization sends `t` to `t`. -/
@[simp]
theorem diagonalSpecialization_X_one :
    diagonalSpecialization (MvPolynomial.X 1) = ratFuncVar ℚ := by
  simp [diagonalSpecialization]

/-- Every Pieri denominator survives the diagonal specialization. -/
theorem pieriDen_diagonalSpecialization_ne_zero (lam : Nat.PartitionVector N) (δ : Strip N) :
    pieriDen lam δ (diagonalSpecialization (MvPolynomial.X 0))
      (diagonalSpecialization (MvPolynomial.X 1)) ≠ 0 := by
  rw [diagonalSpecialization_X_zero, diagonalSpecialization_X_one]
  exact pieriDen_self_ne_zero (fun _ hn ↦ ratFuncVar_pow_ne_one ℚ hn) lam δ

end Diagonal

end PartitionDivision.Macdonald
