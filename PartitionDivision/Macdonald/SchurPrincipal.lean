/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Mathlib.Combinatorics.Enumerative.Partition.Restricted
public import PartitionDivision.TauCeti.Combinatorics.Young.OfRowLens
public import PartitionDivision.TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Schur polynomials indexed by partition vectors, and their principal evaluation

`schurVec R λ` is the Tau Ceti Schur polynomial `TauCeti.diagramSchurPoly` of the Young diagram
whose first `N` rows are the parts of the partition vector `λ`.  The bialternant formula reads
`s_λ · a_δ = a_{λ + δ}` with `δ = (N - 1, …, 1, 0)` (`schurVec_mul_alternant`).

At the principal point `x_i = t ^ (N - 1 - i)` both alternants become Vandermonde determinants
in the values `t ^ (λ_j + N - 1 - j)` and `t ^ (N - 1 - j)`, which are pairwise distinct as soon
as the powers of `t` are.  Hence `s_λ(t ^ (N - 1), …, t, 1) ≠ 0` (`eval_schurVec_ne_zero`).
This is the Schur input of Pieri ledger Lemma 8 (`docs/PIERI.md`).
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace PartitionDivision.Macdonald

open MvPolynomial TauCeti

variable {N : ℕ}

/-- The Young diagram whose first `N` row lengths are the parts of a partition vector. -/
def youngDiagram (lam : Nat.PartitionVector N) : YoungDiagram :=
  YoungDiagram.ofRowLensFin lam lam.antitone

/-- The rows of `youngDiagram λ` are the parts of `λ`. -/
@[simp]
theorem rowLen_youngDiagram (lam : Nat.PartitionVector N) (i : Fin N) :
    (youngDiagram lam).rowLen i = lam i :=
  YoungDiagram.rowLen_ofRowLensFin _ _ i

/-- The diagram of a partition vector has at most `N` rows. -/
theorem colLen_zero_youngDiagram_le (lam : Nat.PartitionVector N) :
    (youngDiagram lam).colLen 0 ≤ N :=
  YoungDiagram.colLen_zero_ofRowLensFin_le _ _

/-- The Schur polynomial in `N` variables indexed by a partition vector. -/
def schurVec (R : Type*) [CommSemiring R] (lam : Nat.PartitionVector N) :
    MvPolynomial (Fin N) R :=
  diagramSchurPoly N R (youngDiagram lam)

/-- The diagram of the empty partition vector is empty. -/
@[simp]
theorem youngDiagram_zero : youngDiagram (0 : Nat.PartitionVector N) = ⊥ := by
  refine YoungDiagram.rowLen_injective (funext fun i ↦ ?_)
  rw [YoungDiagram.rowLen_bot]
  by_cases hi : i < N
  · exact rowLen_youngDiagram 0 ⟨i, hi⟩
  · exact YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le _ _ (Nat.le_of_not_lt hi)

/-- The Schur polynomial of the empty partition vector is one. -/
@[simp]
theorem schurVec_zero (R : Type*) [CommSemiring R] :
    schurVec R (0 : Nat.PartitionVector N) = 1 := by
  rw [schurVec, youngDiagram_zero, diagramSchurPoly_bot]

/-- Coefficient maps commute with `schurVec`. -/
theorem map_schurVec {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (lam : Nat.PartitionVector N) : map f (schurVec R lam) = schurVec S lam :=
  map_diagramSchurPoly f

/-- **Bialternant formula** for partition vectors: `s_λ · a_δ = a_{λ + δ}`. -/
theorem schurVec_mul_alternant (R : Type*) [CommRing R] (lam : Nat.PartitionVector N) :
    schurVec R lam * alternant (Fin N) R (fun j ↦ N - 1 - j) =
      alternant (Fin N) R (fun j ↦ lam j + (N - 1 - j)) := by
  rw [schurVec, diagramSchurPoly_mul_alternant N _ (colLen_zero_youngDiagram_le lam)]
  congr 1
  funext j
  rw [YoungDiagram.betaNumber_def, rowLen_youngDiagram]

/-- The shifted parts `λ_j + N - 1 - j` of a partition vector are pairwise distinct. -/
theorem injective_add_staircase (lam : Nat.PartitionVector N) :
    Function.Injective fun j : Fin N ↦ lam j + (N - 1 - j) := by
  have key (i j : Fin N) (hij : i < j) : lam j + (N - 1 - j) < lam i + (N - 1 - i) := by
    have h := lam.antitone hij.le
    have hj := j.isLt
    have hij' : (i : ℕ) < j := hij
    lia
  intro i j h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd h (key i j hij).ne'
  · exact hij
  · exact absurd h (key j i hij).ne

/-- At the principal point `x_i = t ^ (N - 1 - i)`, an alternant with pairwise distinct exponents
is nonzero, provided the powers of `t` are pairwise distinct.  The evaluated alternant is, up to
sign and transposition, the Vandermonde determinant of the values `t ^ α_j`. -/
theorem eval_alternant_ne_zero {R : Type*} [CommRing R] [IsDomain R] {t : R}
    (ht : Function.Injective fun n : ℕ ↦ t ^ n) {α : Fin N → ℕ} (hα : Function.Injective α) :
    eval (fun i : Fin N ↦ t ^ (N - 1 - (i : ℕ))) (alternant (Fin N) R α) ≠ 0 := by
  have hmat : (eval fun i : Fin N ↦ t ^ (N - 1 - (i : ℕ))).mapMatrix
      (Matrix.of fun i j ↦ (X i : MvPolynomial (Fin N) R) ^ α j) =
      ((Matrix.vandermonde fun j ↦ t ^ α j).submatrix id Fin.revPerm).transpose := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_pow, eval_X,
      Matrix.transpose_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply,
      Fin.revPerm_apply, Fin.val_rev, ← pow_mul]
    congr 1
    have hi := i.isLt
    rw [mul_comm]
    congr 1
    lia
  rw [alternant_def, RingHom.map_det, hmat, Matrix.det_transpose, Matrix.det_permute']
  refine mul_ne_zero ?_ (Matrix.det_vandermonde_ne_zero_iff.mpr (ht.comp hα))
  rcases Int.units_eq_one_or (Equiv.Perm.sign Fin.revPerm) with h | h <;> rw [h] <;> simp

/-- **Principal Schur evaluation.**  If the powers of `t` are pairwise distinct, then
`s_λ(t ^ (N - 1), …, t, 1) ≠ 0`. -/
theorem eval_schurVec_ne_zero {R : Type*} [CommRing R] [IsDomain R] {t : R}
    (ht : Function.Injective fun n : ℕ ↦ t ^ n) (lam : Nat.PartitionVector N) :
    eval (fun i : Fin N ↦ t ^ (N - 1 - (i : ℕ))) (schurVec R lam) ≠ 0 := by
  intro h0
  have h := congrArg (eval fun i : Fin N ↦ t ^ (N - 1 - (i : ℕ))) (schurVec_mul_alternant R lam)
  rw [map_mul, h0, zero_mul] at h
  exact eval_alternant_ne_zero ht (injective_add_staircase lam) h.symm

end PartitionDivision.Macdonald
