/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Mathlib.Combinatorics.Enumerative.Partition.Restricted
public import Mathlib.Algebra.Field.Basic

/-!
# Principal-specialization products for bounded partitions

This file records the cell statistics and the numerator and denominator in Macdonald's
principal-specialization formula VI (6.11).  They are kept as explicit finite products of
binomials `1 - q^a t^b`, so later cancellation arguments do not depend on Macdonald-polynomial
theory.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Nat.PartitionVector.Macdonald

variable {N : ℕ} {K : Type*}

/-- A cell of a bounded partition is a row together with a column below that row's length. -/
abbrev Cell (N : ℕ) := Σ _ : Fin N, ℕ

/-- The cells in the Young diagram of a partition vector. -/
def cells (lam : Nat.PartitionVector N) : Finset (Cell N) :=
  Finset.univ.sigma fun i ↦ Finset.range (lam i)

/-- Membership in the cell finset. -/
@[simp]
theorem mem_cells {lam : Nat.PartitionVector N} {s : Cell N} :
    s ∈ cells lam ↔ s.2 < lam s.1 := by
  simp [cells]

/-- The arm length of a cell. -/
def arm (lam : Nat.PartitionVector N) (s : Cell N) : ℕ :=
  lam s.1 - 1 - s.2

/-- The leg length of a cell. -/
def leg (lam : Nat.PartitionVector N) (s : Cell N) : ℕ :=
  ((Finset.univ.filter fun k : Fin N ↦ s.1 < k ∧ s.2 < lam k).card)

/-- The coarm length of a cell. -/
def coarm (s : Cell N) : ℕ := s.2

/-- The coleg length of a cell, using zero-indexed rows. -/
def coleg (s : Cell N) : ℕ := s.1.val

/-- The statistic `n(lambda) = sum_i i lambda_i` in zero-indexed rows. -/
def nStatistic (lam : Nat.PartitionVector N) : ℕ :=
  ∑ i, i.val * lam i

/-- A binomial factor `1 - q^a t^b` in a principal-specialization product. -/
def specializationBinomial [CommRing K] (q t : K) (a b : ℕ) : K :=
  1 - q ^ a * t ^ b

/-- The numerator in the principal-specialization formula, including `t^n(lambda)`. -/
def principalSpecializationNum [CommRing K] (q t : K)
    (lam : Nat.PartitionVector N) : K :=
  t ^ nStatistic lam *
    ∏ s ∈ cells lam,
      specializationBinomial q t (coarm s) (N - coleg s)

/-- The denominator in the principal-specialization formula. -/
def principalSpecializationDen [CommRing K] (q t : K)
    (lam : Nat.PartitionVector N) : K :=
  ∏ s ∈ cells lam,
    specializationBinomial q t (arm lam s) (leg lam s + 1)

/-- Macdonald's principal-specialization product `Phi(lambda)` from VI (6.11). -/
def principalSpecialization [Field K] (q t : K) (lam : Nat.PartitionVector N) : K :=
  principalSpecializationNum q t lam / principalSpecializationDen q t lam

/-- The principal-specialization denominator is nonzero when all of its explicit binomial
factors are nonzero. -/
theorem principalSpecializationDen_ne_zero [Field K] {q t : K}
    (lam : Nat.PartitionVector N)
    (h : ∀ s ∈ cells lam,
      specializationBinomial q t (arm lam s) (leg lam s + 1) ≠ 0) :
    principalSpecializationDen q t lam ≠ 0 := by
  rw [principalSpecializationDen, Finset.prod_ne_zero_iff]
  intro s hs
  exact h s hs

/-- The principal-specialization numerator is nonzero when `t` and all of its explicit
binomial factors are nonzero. -/
theorem principalSpecializationNum_ne_zero [Field K] {q t : K}
    (lam : Nat.PartitionVector N) (ht : t ≠ 0)
    (h : ∀ s ∈ cells lam,
      specializationBinomial q t (coarm s) (N - coleg s) ≠ 0) :
    principalSpecializationNum q t lam ≠ 0 := by
  rw [principalSpecializationNum]
  apply mul_ne_zero (pow_ne_zero _ ht)
  rw [Finset.prod_ne_zero_iff]
  intro s hs
  exact h s hs

end Nat.PartitionVector.Macdonald
