/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Mathlib.Combinatorics.Enumerative.Partition.Restricted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.NNRat.BigOperators
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.FinCases

/-!
# Row-pair form of the vertical Macdonald--Pieri coefficient

A vertical strip is represented by a function `Fin N → Fin 2`.  This makes its zero-one nature
intrinsic, while `IsLegal` records exactly the additional condition that adding it to a partition
preserves weak decrease.  The numerator and denominator below are the two polynomial products in
the row-pair formula for `ψ'`.
-/

@[expose] public section

open Finset Polynomial

namespace Nat.PartitionVector.Pieri

variable {N : ℕ}

/-- A zero-one vector encoding a vertical strip. -/
abbrev Strip (N : ℕ) := Fin N → Fin 2

private theorem eq_and_eq_zero_and_eq_one_of_le_of_add_lt_add
    (a b : ℕ) (x y : Fin 2) (hba : b ≤ a) (h : a + x.val < b + y.val) :
    a = b ∧ x = 0 ∧ y = 1 := by
  fin_cases x <;> fin_cases y <;> simp_all <;> lia

/-- A vertical strip is legal on `λ` when adding it coordinatewise preserves weak decrease. -/
def IsLegal (lam : Nat.PartitionVector N) (δ : Strip N) : Prop :=
  Antitone fun i ↦ lam i + (δ i : ℕ)

/-- The row pairs that contribute to the vertical Pieri coefficient. -/
def rowPairs (δ : Strip N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun ij ↦ ij.1 < ij.2 ∧ δ ij.1 = 0 ∧ δ ij.2 = 1

/-- Membership in the set of contributing row pairs. -/
@[simp]
theorem mem_rowPairs {δ : Strip N} {ij : Fin N × Fin N} :
    ij ∈ rowPairs δ ↔ ij.1 < ij.2 ∧ δ ij.1 = 0 ∧ δ ij.2 = 1 := by
  simp [rowPairs]

/-- The difference between the parts in a row pair. -/
def rowDifference (lam : Nat.PartitionVector N) (ij : Fin N × Fin N) : ℕ :=
  lam ij.1 - lam ij.2

/-- The positive distance between the indices in a contributing row pair. -/
def rowDistance (ij : Fin N × Fin N) : ℕ := ij.2.val - ij.1.val

/-- The basic binomial `1 - q^a t^b` occurring in Pieri factors. -/
def binomial {R : Type*} [CommRing R] (q t : R) (a b : ℕ) : R :=
  1 - q ^ a * t ^ b

/-- The numerator of the factor belonging to one row pair. -/
def pairNum {R : Type*} [CommRing R] (lam : Nat.PartitionVector N) (q t : R)
    (ij : Fin N × Fin N) : R :=
  binomial q t (rowDifference lam ij) (rowDistance ij - 1) *
    binomial q t (rowDifference lam ij - 1) (rowDistance ij + 1)

/-- The denominator of the factor belonging to one row pair. -/
def pairDen {R : Type*} [CommRing R] (lam : Nat.PartitionVector N) (q t : R)
    (ij : Fin N × Fin N) : R :=
  binomial q t (rowDifference lam ij) (rowDistance ij) *
    binomial q t (rowDifference lam ij - 1) (rowDistance ij)

/-- The numerator polynomial of the row-pair Pieri coefficient. -/
def pieriNum {R : Type*} [CommRing R] (lam : Nat.PartitionVector N) (δ : Strip N)
    (q t : R) : R :=
  ∏ ij ∈ rowPairs δ, pairNum lam q t ij

/-- The denominator polynomial of the row-pair Pieri coefficient. -/
def pieriDen {R : Type*} [CommRing R] (lam : Nat.PartitionVector N) (δ : Strip N)
    (q t : R) : R :=
  ∏ ij ∈ rowPairs δ, pairDen lam q t ij

/-- Legality makes the part difference of every contributing row pair strictly positive. -/
theorem rowDifference_pos {lam : Nat.PartitionVector N} {δ : Strip N}
    (hδ : IsLegal lam δ) {ij : Fin N × Fin N} (hij : ij ∈ rowPairs δ) :
    0 < rowDifference lam ij := by
  rw [mem_rowPairs] at hij
  have h := hδ (Fin.le_of_lt hij.1)
  simp only [hij.2.1, hij.2.2, Fin.val_zero, Fin.val_one, add_zero] at h
  exact Nat.sub_pos_of_lt h

/-- The index distance of every contributing row pair is strictly positive. -/
theorem rowDistance_pos {δ : Strip N} {ij : Fin N × Fin N} (hij : ij ∈ rowPairs δ) :
    0 < rowDistance ij := by
  rw [mem_rowPairs] at hij
  exact Nat.sub_pos_of_lt hij.1

/-- Ring homomorphisms commute with the basic Pieri binomial. -/
theorem map_binomial {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (q t : R) (a b : ℕ) : f (binomial q t a b) = binomial (f q) (f t) a b := by
  simp [binomial]

/-- Ring homomorphisms commute with a row-pair numerator. -/
theorem map_pairNum {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (lam : Nat.PartitionVector N) (q t : R) (ij : Fin N × Fin N) :
    f (pairNum lam q t ij) = pairNum lam (f q) (f t) ij := by
  simp [pairNum, map_binomial]

/-- Ring homomorphisms commute with a row-pair denominator. -/
theorem map_pairDen {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (lam : Nat.PartitionVector N) (q t : R) (ij : Fin N × Fin N) :
    f (pairDen lam q t ij) = pairDen lam (f q) (f t) ij := by
  simp [pairDen, map_binomial]

/-- Ring homomorphisms commute with the Pieri numerator. -/
theorem map_pieriNum {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (lam : Nat.PartitionVector N) (δ : Strip N) (q t : R) :
    f (pieriNum lam δ q t) = pieriNum lam δ (f q) (f t) := by
  simp [pieriNum, map_pairNum]

/-- Ring homomorphisms commute with the Pieri denominator. -/
theorem map_pieriDen {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (lam : Nat.PartitionVector N) (δ : Strip N) (q t : R) :
    f (pieriDen lam δ q t) = pieriDen lam δ (f q) (f t) := by
  simp [pieriDen, map_pairDen]

/-- At `t = X`, a basic binomial with positive `X`-exponent evaluates to one at zero. -/
theorem eval_zero_binomial_C_X {F : Type*} [Field F] (z : F) (a b : ℕ) (hb : 0 < b) :
    (binomial (C z) X a b : F[X]).eval 0 = 1 := by
  simp [binomial, hb.ne']

/-- At `q = ζ` and `t = X`, each denominator row-pair factor evaluates to one at zero. -/
theorem eval_zero_pairDen_C_X {F : Type*} [Field F] (ζ : F)
    (lam : Nat.PartitionVector N) {δ : Strip N} {ij : Fin N × Fin N}
    (hij : ij ∈ rowPairs δ) : (pairDen lam (C ζ) X ij : F[X]).eval 0 = 1 := by
  rw [pairDen, eval_mul, eval_zero_binomial_C_X _ _ _ (rowDistance_pos hij),
    eval_zero_binomial_C_X _ _ _ (rowDistance_pos hij), one_mul]

/-- The specialized Pieri denominator evaluates to one at zero. -/
theorem eval_zero_pieriDen_C_X {F : Type*} [Field F] (ζ : F)
    (lam : Nat.PartitionVector N) (δ : Strip N) :
    (pieriDen lam δ (C ζ) X : F[X]).eval 0 = 1 := by
  rw [pieriDen, eval_prod]
  apply Finset.prod_eq_one
  intro ij hij
  exact eval_zero_pairDen_C_X ζ lam hij

/-- The denominator of the Pieri coefficient is nonzero after specializing `q = ζ`, `t = X`. -/
theorem pieriDen_C_X_ne_zero {F : Type*} [Field F] (ζ : F)
    (lam : Nat.PartitionVector N) (δ : Strip N) :
    pieriDen lam δ (C ζ) X ≠ (0 : F[X]) := by
  intro h
  have := eval_zero_pieriDen_C_X ζ lam δ
  rw [h, eval_zero] at this
  exact zero_ne_one this

/-- The partition `(1^h)` padded to `N` coordinates. -/
def prefixOnes (h : ℕ) : Nat.PartitionVector N where
  val i := if i.val < h then 1 else 0
  property i j hij := by
    by_cases hj : j.val < h
    · have hi : i.val < h := lt_of_le_of_lt hij hj
      simp [hi, hj]
    · simp [hj]

/-- Evaluation of the padded partition `(1^h)`. -/
@[simp]
theorem prefixOnes_apply (h : ℕ) (i : Fin N) :
    prefixOnes h i = if i.val < h then 1 else 0 := rfl

/-- Add `k` to the first `h` coordinates of a partition vector. -/
def addRectangle (lam : Nat.PartitionVector N) (k h : ℕ) : Nat.PartitionVector N :=
  lam + k • prefixOnes h

/-- Coordinate formula for adding a rectangle. -/
@[simp]
theorem addRectangle_apply (lam : Nat.PartitionVector N) (k h : ℕ) (i : Fin N) :
    addRectangle lam k h i = lam i + if i.val < h then k else 0 := by
  simp [addRectangle]

/-- Adding a rectangle preserves legality of a vertical strip. -/
theorem IsLegal.addRectangle {lam : Nat.PartitionVector N} {δ : Strip N}
    (hδ : IsLegal lam δ) (k h : ℕ) : IsLegal (addRectangle lam k h) δ := by
  intro i j hij
  have hbase := hδ hij
  have hpref : (if j.val < h then k else 0) ≤ (if i.val < h then k else 0) := by
    by_cases hj : j.val < h
    · have hi : i.val < h := lt_of_le_of_lt hij hj
      simp [hi, hj]
    · simp [hj]
  simp only [addRectangle_apply]
  simpa only [add_assoc, add_left_comm, add_comm] using Nat.add_le_add hbase hpref

/-- A rectangle changes a row difference by `k` exactly when the row pair crosses its lower
boundary. -/
theorem rowDifference_addRectangle (lam : Nat.PartitionVector N) (k h : ℕ)
    (ij : Fin N × Fin N) (hij : ij.1 ≤ ij.2) :
    rowDifference (addRectangle lam k h) ij =
      rowDifference lam ij + if ij.1.val < h ∧ h ≤ ij.2.val then k else 0 := by
  have hlam := lam.antitone hij
  by_cases hi : ij.1.val < h
  · by_cases hj : ij.2.val < h
    · have hnj : ¬h ≤ ij.2.val := Nat.not_le_of_lt hj
      simpa [rowDifference, hi, hj, hnj] using
        Nat.add_sub_add_right (lam ij.1) k (lam ij.2)
    · have hjle : h ≤ ij.2.val := Nat.le_of_not_gt hj
      simpa [rowDifference, hi, hj, hjle] using Nat.sub_add_comm hlam
  · by_cases hj : ij.2.val < h
    · exact (hi (lt_of_le_of_lt hij hj)).elim
    · simp [rowDifference, hi, hj]

/-- Subtracting one from a positive row difference commutes with the rectangular change. -/
theorem rowDifference_addRectangle_sub_one (lam : Nat.PartitionVector N) (k h : ℕ)
    (ij : Fin N × Fin N) (hij : ij.1 ≤ ij.2) (hdiff : 0 < rowDifference lam ij) :
    rowDifference (addRectangle lam k h) ij - 1 =
      (rowDifference lam ij - 1) + if ij.1.val < h ∧ h ≤ ij.2.val then k else 0 := by
  rw [rowDifference_addRectangle lam k h ij hij]
  split
  · exact Nat.sub_add_comm (Nat.one_le_iff_ne_zero.mpr hdiff.ne')
  · simp

/-- Powers of a `k`th root of unity do not see the rectangular change in a row difference. -/
theorem pow_rowDifference_addRectangle {R : Type*} [CommRing R] (ζ : R) (hζ : ζ ^ k = 1)
    (lam : Nat.PartitionVector N) (h : ℕ) (ij : Fin N × Fin N) (hij : ij.1 ≤ ij.2) :
    ζ ^ rowDifference (addRectangle lam k h) ij = ζ ^ rowDifference lam ij := by
  rw [rowDifference_addRectangle lam k h ij hij]
  split
  · simp only [pow_add, hζ, mul_one]
  · simp

/-- Powers of a `k`th root of unity also do not see the change after subtracting one from a
positive row difference. -/
theorem pow_rowDifference_addRectangle_sub_one {R : Type*} [CommRing R]
    (ζ : R) (hζ : ζ ^ k = 1) (lam : Nat.PartitionVector N) (h : ℕ)
    (ij : Fin N × Fin N) (hij : ij.1 ≤ ij.2) (hdiff : 0 < rowDifference lam ij) :
    ζ ^ (rowDifference (addRectangle lam k h) ij - 1) =
      ζ ^ (rowDifference lam ij - 1) := by
  rw [rowDifference_addRectangle_sub_one lam k h ij hij hdiff]
  split
  · simp only [pow_add, hζ, mul_one]
  · simp

/-- At a `k`th root of unity, a legal row-pair numerator is unchanged by adding a rectangle. -/
theorem pairNum_addRectangle_eq {R : Type*} [CommRing R] (ζ t : R) (hζ : ζ ^ k = 1)
    {lam : Nat.PartitionVector N} {δ : Strip N} (hδ : IsLegal lam δ) (h : ℕ)
    {ij : Fin N × Fin N} (hij : ij ∈ rowPairs δ) :
    pairNum (addRectangle lam k h) ζ t ij = pairNum lam ζ t ij := by
  have hle := Fin.le_of_lt (mem_rowPairs.mp hij).1
  simp only [pairNum, binomial]
  rw [pow_rowDifference_addRectangle ζ hζ lam h ij hle,
    pow_rowDifference_addRectangle_sub_one ζ hζ lam h ij hle (rowDifference_pos hδ hij)]

/-- At a `k`th root of unity, a legal row-pair denominator is unchanged by adding a rectangle. -/
theorem pairDen_addRectangle_eq {R : Type*} [CommRing R] (ζ t : R) (hζ : ζ ^ k = 1)
    {lam : Nat.PartitionVector N} {δ : Strip N} (hδ : IsLegal lam δ) (h : ℕ)
    {ij : Fin N × Fin N} (hij : ij ∈ rowPairs δ) :
    pairDen (addRectangle lam k h) ζ t ij = pairDen lam ζ t ij := by
  have hle := Fin.le_of_lt (mem_rowPairs.mp hij).1
  simp only [pairDen, binomial]
  rw [pow_rowDifference_addRectangle ζ hζ lam h ij hle,
    pow_rowDifference_addRectangle_sub_one ζ hζ lam h ij hle (rowDifference_pos hδ hij)]

/-- At a `k`th root of unity, the Pieri numerator is periodic under rectangular shifts. -/
theorem pieriNum_addRectangle_eq {R : Type*} [CommRing R] (ζ t : R) (hζ : ζ ^ k = 1)
    {lam : Nat.PartitionVector N} {δ : Strip N} (hδ : IsLegal lam δ) (h : ℕ) :
    pieriNum (addRectangle lam k h) δ ζ t = pieriNum lam δ ζ t := by
  apply Finset.prod_congr rfl
  intro ij hij
  exact pairNum_addRectangle_eq ζ t hζ hδ h hij

/-- At a `k`th root of unity, the Pieri denominator is periodic under rectangular shifts. -/
theorem pieriDen_addRectangle_eq {R : Type*} [CommRing R] (ζ t : R) (hζ : ζ ^ k = 1)
    {lam : Nat.PartitionVector N} {δ : Strip N} (hδ : IsLegal lam δ) (h : ℕ) :
    pieriDen (addRectangle lam k h) δ ζ t = pieriDen lam δ ζ t := by
  apply Finset.prod_congr rfl
  intro ij hij
  exact pairDen_addRectangle_eq ζ t hζ hδ h hij

/-- Polynomial form of periodicity for the Pieri numerator at `(q,t) = (C ζ,X)`. -/
theorem pieriNum_addRectangle_C_X_eq {F : Type*} [Field F] (ζ : F) (hζ : ζ ^ k = 1)
    {lam : Nat.PartitionVector N} {δ : Strip N} (hδ : IsLegal lam δ) (h : ℕ) :
    pieriNum (addRectangle lam k h) δ (C ζ) X = pieriNum lam δ (C ζ) X := by
  exact pieriNum_addRectangle_eq (C ζ) X (by simpa using congrArg C hζ) hδ h

/-- Polynomial form of periodicity for the Pieri denominator at `(q,t) = (C ζ,X)`. -/
theorem pieriDen_addRectangle_C_X_eq {F : Type*} [Field F] (ζ : F) (hζ : ζ ^ k = 1)
    {lam : Nat.PartitionVector N} {δ : Strip N} (hδ : IsLegal lam δ) (h : ℕ) :
    pieriDen (addRectangle lam k h) δ (C ζ) X = pieriDen lam δ (C ζ) X := by
  exact pieriDen_addRectangle_eq (C ζ) X (by simpa using congrArg C hζ) hδ h

/-- If adding a rectangle makes a previously illegal strip legal, the two rows across the lower
boundary form a contributing pair, have shifted difference `k`, and have distance one. -/
theorem exists_boundary_pair_of_addRectangle_legal_of_not_legal
    {lam : Nat.PartitionVector N} {δ : Strip N} {k h : ℕ} (hh : 1 ≤ h)
    (hshift : IsLegal (addRectangle lam k h) δ) (hbad : ¬IsLegal lam δ) :
    ∃ ij ∈ rowPairs δ,
      rowDifference (addRectangle lam k h) ij = k ∧ rowDistance ij = 1 := by
  rw [IsLegal] at hbad
  simp only [Antitone] at hbad
  push Not at hbad
  obtain ⟨i, j, hij, hbad⟩ := hbad
  have hshiftij := hshift hij
  have hi : i.val < h := by
    by_contra hi
    have hii : h ≤ i.val := Nat.le_of_not_gt hi
    have hijj : h ≤ j.val := hii.trans hij
    exact (not_lt_of_ge (by
      simpa [addRectangle_apply, hii.not_gt, hijj.not_gt] using hshiftij)) hbad
  have hj : h ≤ j.val := by
    by_contra hj
    have hjj : j.val < h := Nat.lt_of_not_ge hj
    have hii : i.val < h := lt_of_le_of_lt hij hjj
    exact (not_lt_of_ge (by
      simpa [addRectangle_apply, hii, hjj, add_assoc, add_left_comm, add_comm] using
        hshiftij)) hbad
  have hpart := lam.antitone hij
  obtain ⟨hlamij, hδi, hδj⟩ :=
    eq_and_eq_zero_and_eq_one_of_le_of_add_lt_add (lam i) (lam j) (δ i) (δ j)
      hpart hbad
  have hhN' : h < N := lt_of_le_of_lt hj j.isLt
  let a : Fin N := ⟨h - 1, by lia⟩
  let b : Fin N := ⟨h, hhN'⟩
  have hi_a : i ≤ a := by
    change i.val ≤ h - 1
    lia
  have ha_b : a < b := by
    change h - 1 < h
    lia
  have hb_j : b ≤ j := hj
  have hlamia := lam.antitone hi_a
  have hlambj := lam.antitone hb_j
  have hlamab := lam.antitone ha_b.le
  have hlamai : lam a = lam i := by lia
  have hlambj' : lam b = lam j := by lia
  have hlamab' : lam a = lam b := by lia
  have hshiftia := hshift hi_a
  have hshiftbj := hshift hb_j
  have hδa : δ a = 0 := by
    apply Fin.ext
    have hda := (δ a).isLt
    simp [addRectangle_apply, a, hi, hδi] at hshiftia
    simp only [Fin.val_zero]
    lia
  have hδb : δ b = 1 := by
    apply Fin.ext
    have hdb := (δ b).isLt
    simp [addRectangle_apply, b, hδj] at hshiftbj
    simp only [Fin.val_one]
    lia
  refine ⟨(a, b), ?_, ?_, ?_⟩
  · exact mem_rowPairs.mpr ⟨ha_b, hδa, hδb⟩
  · have hpred : h - 1 < h := by lia
    simp [rowDifference, addRectangle_apply, a, b, hpred, hlamab']
  · change h - (h - 1) = 1
    lia

/-- At a `k`th root of unity, the numerator of a strip made legal only by a rectangular shift
vanishes. -/
theorem pieriNum_addRectangle_eq_zero_of_not_legal {R : Type*} [CommRing R]
    (ζ t : R) (hζ : ζ ^ k = 1) {lam : Nat.PartitionVector N} {δ : Strip N}
    {h : ℕ} (hh : 1 ≤ h) (hshift : IsLegal (addRectangle lam k h) δ)
    (hbad : ¬IsLegal lam δ) : pieriNum (addRectangle lam k h) δ ζ t = 0 := by
  obtain ⟨ij, hij, hdiff, hdist⟩ :=
    exists_boundary_pair_of_addRectangle_legal_of_not_legal hh hshift hbad
  rw [pieriNum]
  apply Finset.prod_eq_zero hij
  simp [pairNum, binomial, hdiff, hdist, hζ]

/-- Polynomial form of vanishing for a strip made legal only by a rectangular shift. -/
theorem pieriNum_addRectangle_C_X_eq_zero_of_not_legal {F : Type*} [Field F]
    (ζ : F) (hζ : ζ ^ k = 1) {lam : Nat.PartitionVector N} {δ : Strip N}
    {h : ℕ} (hh : 1 ≤ h) (hshift : IsLegal (addRectangle lam k h) δ)
    (hbad : ¬IsLegal lam δ) : pieriNum (addRectangle lam k h) δ (C ζ) X = 0 := by
  exact pieriNum_addRectangle_eq_zero_of_not_legal (C ζ) X
    (by simpa using congrArg C hζ) hh hshift hbad

/-- The root-of-unity binomial `1 - C(ζ^c) X^n`. -/
noncomputable def rootBinomial {F : Type*} [Field F] (ζ : F) (c n : ℕ) : F[X] :=
  1 - C (ζ ^ c) * X ^ n

/-- If the root-of-unity coefficient is one and the `X`-exponent is zero, the root binomial is
identically zero. -/
theorem rootBinomial_zero {F : Type*} [Field F] (ζ : F) (c : ℕ) (h : ζ ^ c = 1) :
    rootBinomial ζ c 0 = 0 := by
  simp [rootBinomial, h]

/-- After substituting `q = ζ` and `t = ζ X`, a Pieri binomial depends on the sum of its
`q`- and `t`-exponents. -/
theorem binomial_C_C_mul_X {F : Type*} [Field F] (ζ : F) (a b : ℕ) :
    binomial (C ζ) (C ζ * X) a b = rootBinomial ζ (a + b) b := by
  simp only [binomial, rootBinomial, mul_pow, map_pow]
  congr 1
  rw [← mul_assoc, ← pow_add]

/-- Normal form of a specialized numerator row-pair factor, grouped by equal powers of `ζ`. -/
theorem pairNum_C_C_mul_X {F : Type*} [Field F] (ζ : F)
    {lam : Nat.PartitionVector N} {δ : Strip N} {ij : Fin N × Fin N}
    (hδ : IsLegal lam δ) (hij : ij ∈ rowPairs δ) :
    pairNum lam (C ζ) (C ζ * X) ij =
      rootBinomial ζ (rowDifference lam ij + rowDistance ij - 1) (rowDistance ij - 1) *
      rootBinomial ζ (rowDifference lam ij + rowDistance ij) (rowDistance ij + 1) := by
  rw [pairNum, binomial_C_C_mul_X, binomial_C_C_mul_X]
  congr 2 <;> have hd := rowDifference_pos hδ hij <;>
    have hm := rowDistance_pos hij <;> lia

/-- Normal form of a specialized denominator row-pair factor, grouped by equal powers of `ζ`. -/
theorem pairDen_C_C_mul_X {F : Type*} [Field F] (ζ : F)
    {lam : Nat.PartitionVector N} {δ : Strip N} {ij : Fin N × Fin N}
    (hδ : IsLegal lam δ) (hij : ij ∈ rowPairs δ) :
    pairDen lam (C ζ) (C ζ * X) ij =
      rootBinomial ζ (rowDifference lam ij + rowDistance ij)
          (rowDistance ij) *
      rootBinomial ζ (rowDifference lam ij + rowDistance ij - 1)
          (rowDistance ij) := by
  rw [pairDen, binomial_C_C_mul_X, binomial_C_C_mul_X]
  congr 2
  have hd := rowDifference_pos hδ hij
  have hm := rowDistance_pos hij
  lia

/-- The nonnegative rational selected by a root-of-unity binomial quotient. -/
def rootRatioWeight (k c n m : ℕ) : ℚ≥0 :=
  if k ∣ c then (n : ℚ≥0) / m else 1

/-- A root-of-unity binomial quotient has a presentation regular at one whose value is the cast
of `rootRatioWeight`. -/
theorem exists_rootRatio_regularPresentation {F : Type*} [Field F] [CharZero F]
    {ζ : F} {k : ℕ} (hζ : IsPrimitiveRoot ζ k) (c n m : ℕ) (hm : 0 < m) :
    ∃ p r : F[X], rootBinomial ζ c n * r = rootBinomial ζ c m * p ∧
      r.eval 1 ≠ 0 ∧ p.eval 1 / r.eval 1 = (rootRatioWeight k c n m : F) := by
  by_cases hc : k ∣ c
  · have hpow : ζ ^ c = 1 := (hζ.pow_eq_one_iff_dvd c).mpr hc
    refine ⟨∑ i ∈ Finset.range n, X ^ i, ∑ i ∈ Finset.range m, X ^ i, ?_, ?_, ?_⟩
    · simp only [rootBinomial, hpow, map_one, one_mul]
      rw [show (1 - X ^ n : F[X]) =
          (∑ i ∈ Finset.range n, X ^ i) * (1 - X) by
        simpa using (geom_sum_mul_neg (X : F[X]) n).symm]
      rw [show (1 - X ^ m : F[X]) =
          (∑ i ∈ Finset.range m, X ^ i) * (1 - X) by
        simpa using (geom_sum_mul_neg (X : F[X]) m).symm]
      ac_rfl
    · simp only [eval_finsetSum, eval_pow, eval_X, one_pow, sum_const, card_range,
        nsmul_eq_mul, mul_one, Nat.cast_ne_zero]
      exact Nat.ne_of_gt hm
    · simp [rootRatioWeight, hc]
  · have hpow : ζ ^ c ≠ 1 := (hζ.pow_eq_one_iff_dvd c).not.mpr hc
    refine ⟨rootBinomial ζ c n, rootBinomial ζ c m, mul_comm _ _, ?_, ?_⟩
    · simpa [rootBinomial] using sub_ne_zero.mpr (Ne.symm hpow)
    · simp [rootBinomial, rootRatioWeight, hc, sub_ne_zero.mpr (Ne.symm hpow)]

/-- The first grouped quotient in a row-pair factor has weight zero, one, or `(m-1)/m`. -/
theorem rootRatioWeight_pred (k c m : ℕ) :
    rootRatioWeight k c (m - 1) m = 0 ∨ rootRatioWeight k c (m - 1) m = 1 ∨
      rootRatioWeight k c (m - 1) m = ((m - 1 : ℕ) : ℚ≥0) / m := by
  by_cases hc : k ∣ c
  · exact Or.inr (Or.inr (by simp [rootRatioWeight, hc]))
  · exact Or.inr (Or.inl (by simp [rootRatioWeight, hc]))

/-- The second grouped quotient in a row-pair factor has weight one or `(m+1)/m`. -/
theorem rootRatioWeight_succ (k c m : ℕ) :
    rootRatioWeight k c (m + 1) m = 1 ∨
      rootRatioWeight k c (m + 1) m = ((m + 1 : ℕ) : ℚ≥0) / m := by
  by_cases hc : k ∣ c
  · exact Or.inr (by simp [rootRatioWeight, hc])
  · exact Or.inl (by simp [rootRatioWeight, hc])

/-- Each specialized row-pair quotient has a presentation regular at one and a value which is
the cast of a nonnegative rational. -/
theorem exists_pair_regularPresentation {F : Type*} [Field F] [CharZero F]
    {ζ : F} {k : ℕ} (hζ : IsPrimitiveRoot ζ k) {lam : Nat.PartitionVector N}
    {δ : Strip N} (hδ : IsLegal lam δ) {ij : Fin N × Fin N}
    (hij : ij ∈ rowPairs δ) :
    ∃ p r : F[X], ∃ w : ℚ≥0,
      pairNum lam (C ζ) (C ζ * X) ij * r =
        pairDen lam (C ζ) (C ζ * X) ij * p ∧
      r.eval 1 ≠ 0 ∧ p.eval 1 / r.eval 1 = (w : F) := by
  let d := rowDifference lam ij
  let m := rowDistance ij
  let c₁ := d + m - 1
  let c₂ := d + m
  have hm : 0 < m := rowDistance_pos hij
  obtain ⟨p₁, r₁, hcross₁, hr₁, hvalue₁⟩ :=
    exists_rootRatio_regularPresentation hζ c₁ (m - 1) m hm
  obtain ⟨p₂, r₂, hcross₂, hr₂, hvalue₂⟩ :=
    exists_rootRatio_regularPresentation hζ c₂ (m + 1) m hm
  refine ⟨p₁ * p₂, r₁ * r₂, rootRatioWeight k c₁ (m - 1) m *
    rootRatioWeight k c₂ (m + 1) m, ?_, ?_, ?_⟩
  · rw [pairNum_C_C_mul_X ζ hδ hij, pairDen_C_C_mul_X ζ hδ hij]
    change (rootBinomial ζ c₁ (m - 1) * rootBinomial ζ c₂ (m + 1)) *
        (r₁ * r₂) =
      (rootBinomial ζ c₂ m * rootBinomial ζ c₁ m) * (p₁ * p₂)
    calc
      _ = (rootBinomial ζ c₁ (m - 1) * r₁) *
          (rootBinomial ζ c₂ (m + 1) * r₂) := by ac_rfl
      _ = (rootBinomial ζ c₁ m * p₁) * (rootBinomial ζ c₂ m * p₂) := by
        rw [hcross₁, hcross₂]
      _ = _ := by ac_rfl
  · rw [eval_mul]
    exact mul_ne_zero hr₁ hr₂
  · rw [eval_mul, eval_mul]
    calc
      p₁.eval 1 * p₂.eval 1 / (r₁.eval 1 * r₂.eval 1) =
          (p₁.eval 1 / r₁.eval 1) * (p₂.eval 1 / r₂.eval 1) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ac_rfl
      _ = (rootRatioWeight k c₁ (m - 1) m : F) *
          (rootRatioWeight k c₂ (m + 1) m : F) := by rw [hvalue₁, hvalue₂]
      _ = ((rootRatioWeight k c₁ (m - 1) m *
          rootRatioWeight k c₂ (m + 1) m : ℚ≥0) : F) := by simp

/-- The complete specialized Pieri quotient has a presentation regular at one whose value is a
nonnegative rational.  Thus the `v → 1` value after `q = ζ`, `t = ζ v` is regular and
nonnegative. -/
theorem exists_pieri_regularPresentation {F : Type*} [Field F] [CharZero F]
    {ζ : F} {k : ℕ} (hζ : IsPrimitiveRoot ζ k) {lam : Nat.PartitionVector N}
    {δ : Strip N} (hδ : IsLegal lam δ) :
    ∃ p r : F[X], ∃ w : ℚ≥0,
      pieriNum lam δ (C ζ) (C ζ * X) * r =
        pieriDen lam δ (C ζ) (C ζ * X) * p ∧
      r.eval 1 ≠ 0 ∧ p.eval 1 / r.eval 1 = (w : F) := by
  have aux : ∀ s : Finset (Fin N × Fin N), s ⊆ rowPairs δ →
      ∃ p r : F[X], ∃ w : ℚ≥0,
        (∏ ij ∈ s, pairNum lam (C ζ) (C ζ * X) ij) * r =
          (∏ ij ∈ s, pairDen lam (C ζ) (C ζ * X) ij) * p ∧
        r.eval 1 ≠ 0 ∧ p.eval 1 / r.eval 1 = (w : F) := by
    intro s hs
    induction s using Finset.induction with
    | empty =>
        exact ⟨1, 1, 1, by simp⟩
    | @insert ij s hijs ih =>
        have hij : ij ∈ rowPairs δ := hs (Finset.mem_insert_self ij s)
        have hss : s ⊆ rowPairs δ := fun x hx ↦ hs (Finset.mem_insert_of_mem hx)
        obtain ⟨p₁, r₁, w₁, hcross₁, hr₁, hvalue₁⟩ :=
          exists_pair_regularPresentation hζ hδ hij
        obtain ⟨p₂, r₂, w₂, hcross₂, hr₂, hvalue₂⟩ := ih hss
        refine ⟨p₁ * p₂, r₁ * r₂, w₁ * w₂, ?_, ?_, ?_⟩
        · simp only [Finset.prod_insert hijs]
          calc
            (pairNum lam (C ζ) (C ζ * X) ij *
                ∏ x ∈ s, pairNum lam (C ζ) (C ζ * X) x) * (r₁ * r₂) =
                (pairNum lam (C ζ) (C ζ * X) ij * r₁) *
                  ((∏ x ∈ s, pairNum lam (C ζ) (C ζ * X) x) * r₂) := by ac_rfl
            _ = (pairDen lam (C ζ) (C ζ * X) ij * p₁) *
                ((∏ x ∈ s, pairDen lam (C ζ) (C ζ * X) x) * p₂) := by
              rw [hcross₁, hcross₂]
            _ = (pairDen lam (C ζ) (C ζ * X) ij *
                ∏ x ∈ s, pairDen lam (C ζ) (C ζ * X) x) * (p₁ * p₂) := by ac_rfl
        · rw [eval_mul]
          exact mul_ne_zero hr₁ hr₂
        · rw [eval_mul, eval_mul]
          calc
            p₁.eval 1 * p₂.eval 1 / (r₁.eval 1 * r₂.eval 1) =
                (p₁.eval 1 / r₁.eval 1) * (p₂.eval 1 / r₂.eval 1) := by
              simp only [div_eq_mul_inv, mul_inv_rev]
              ac_rfl
            _ = (w₁ : F) * (w₂ : F) := by rw [hvalue₁, hvalue₂]
            _ = ((w₁ * w₂ : ℚ≥0) : F) := by simp
  simpa only [pieriNum, pieriDen] using aux (rowPairs δ) (fun _ ↦ id)

end Nat.PartitionVector.Pieri
