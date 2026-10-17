/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Macdonald.GridEvaluation
public import PartitionDivision.Macdonald.PieriCoefficient
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Row form of the Macdonald principal specialization

This file defines Macdonald's principal specialization in the finite row form VI (6.11').
The finite `q`-Pochhammer factors make the first-column recurrence and the cancellation with
the row-pair Pieri coefficient explicit.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Nat.PartitionVector.Macdonald

variable {N : ℕ} {K : Type*}

/-- The statistic `n(lambda) = sum_i i lambda_i` in zero-indexed rows. -/
def nStatistic (lam : Nat.PartitionVector N) : ℕ :=
  ∑ i, i.val * lam i

/-- A binomial factor `1 - q^a t^b`. -/
def specializationBinomial [CommRing K] (q t : K) (a b : ℕ) : K :=
  1 - q ^ a * t ^ b

/-- The finite `q`-Pochhammer product `(t^b;q)_d`. -/
def specializationPochhammer [CommRing K] (q t : K) (b d : ℕ) : K :=
  ∏ a ∈ Finset.range d, specializationBinomial q t a b

/-- The set of ordered row pairs `i < j`. -/
def orderedRowPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ij ↦ ij.1 < ij.2

/-- Membership in the set of ordered row pairs. -/
@[simp]
theorem mem_orderedRowPairs {ij : Fin N × Fin N} :
    ij ∈ orderedRowPairs N ↔ ij.1 < ij.2 := by
  simp [orderedRowPairs]

/-- The row-pair factor in Macdonald's principal-specialization product. -/
def principalRowFactor [Field K] (q t : K) (lam : Nat.PartitionVector N)
    (ij : Fin N × Fin N) : K :=
  specializationPochhammer q t (Nat.PartitionVector.Pieri.rowDistance ij + 1)
      (Nat.PartitionVector.Pieri.rowDifference lam ij) /
    specializationPochhammer q t (Nat.PartitionVector.Pieri.rowDistance ij)
      (Nat.PartitionVector.Pieri.rowDifference lam ij)

/-- Macdonald's principal specialization `Phi(lambda)` in the finite row form VI (6.11'). -/
def principalSpecialization [Field K] (q t : K) (lam : Nat.PartitionVector N) : K :=
  t ^ nStatistic lam *
    ∏ ij ∈ orderedRowPairs N, principalRowFactor q t lam ij

/-- The rows in the initial segment of length `r`. -/
def prefixRows (N r : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ i.val < r

/-- Membership in an initial segment of rows. -/
@[simp]
theorem mem_prefixRows {i : Fin N} : i ∈ prefixRows N r ↔ i.val < r := by
  simp [prefixRows]

/-- The zero-one strip associated to a finset of rows. -/
def stripOfFinset (I : Finset (Fin N)) : Nat.PartitionVector.Pieri.Strip N :=
  fun i ↦ if i ∈ I then 1 else 0

/-- The strip associated to a finset takes value one precisely on that finset. -/
@[simp]
theorem stripOfFinset_eq_one_iff (I : Finset (Fin N)) (i : Fin N) :
    stripOfFinset I i = 1 ↔ i ∈ I := by
  simp [stripOfFinset]

/-- The strip associated to a finset takes value zero precisely off that finset. -/
@[simp]
theorem stripOfFinset_eq_zero_iff (I : Finset (Fin N)) (i : Fin N) :
    stripOfFinset I i = 0 ↔ i ∉ I := by
  simp [stripOfFinset]

/-- Finset legality agrees with legality of its zero-one strip. -/
theorem isLegal_stripOfFinset_iff (mu : Nat.PartitionVector N) (I : Finset (Fin N)) :
    Nat.PartitionVector.Pieri.IsLegal mu (stripOfFinset I) ↔ IsLegal mu I := by
  have hval (i : Fin N) :
      (stripOfFinset I i : ℕ) = if i ∈ I then 1 else 0 := by
    by_cases hi : i ∈ I <;> simp [stripOfFinset, hi]
  constructor
  · intro h i j hij
    simpa [Nat.PartitionVector.Pieri.IsLegal, hval, IsLegal, increment] using h hij
  · intro h i j hij
    simpa [Nat.PartitionVector.Pieri.IsLegal, hval, IsLegal, increment] using h hij

/-- Every initial segment of rows is a legal increment. -/
theorem isLegal_prefixRows (mu : Nat.PartitionVector N) (r : ℕ) :
    IsLegal mu (prefixRows N r) := by
  rw [isLegal_iff_no_bad_pair]
  intro i hi j hj hbad
  rw [mem_prefixRows] at hi
  simp only [prefixRows, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  lia

/-- Adding one to an initial segment of rows. -/
def incrementPrefix (mu : Nat.PartitionVector N) (r : ℕ) : Nat.PartitionVector N :=
  incrementPartition mu (prefixRows N r) (isLegal_prefixRows mu r)

/-- Coordinate formula for adding one to an initial segment of rows. -/
@[simp]
theorem incrementPrefix_apply (mu : Nat.PartitionVector N) (r : ℕ) (i : Fin N) :
    incrementPrefix mu r i = mu i + if i.val < r then 1 else 0 := by
  simp [incrementPrefix]

/-- A positive `t`-exponent makes a specialization binomial nonzero for power-pair injective
parameters. -/
theorem specializationBinomial_ne_zero [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (a b : ℕ) (hb : 0 < b) :
    specializationBinomial q t a b ≠ 0 := by
  rw [specializationBinomial, sub_ne_zero]
  intro h
  have hexp := hqt (a₁ := (0, 0)) (a₂ := (a, b)) (by simpa using h)
  exact hb.ne' (congrArg Prod.snd hexp).symm

/-- A specialization binomial is nonzero when its exponent pair is not `(0,0)`. -/
theorem specializationBinomial_ne_zero_of_ne [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (a b : ℕ) (hab : (a, b) ≠ (0, 0)) :
    specializationBinomial q t a b ≠ 0 := by
  rw [specializationBinomial, sub_ne_zero]
  intro h
  apply hab
  exact hqt (a₁ := (a, b)) (a₂ := (0, 0)) (by simpa using h.symm)

/-- Appending the last factor to a finite `q`-Pochhammer product. -/
theorem specializationPochhammer_succ [CommRing K] (q t : K) (b d : ℕ) :
    specializationPochhammer q t b (d + 1) =
      specializationPochhammer q t b d * specializationBinomial q t d b := by
  simp [specializationPochhammer, Finset.prod_range_succ]

/-- Every finite `q`-Pochhammer factor with positive `t`-exponent is nonzero at power-pair
injective parameters. -/
theorem specializationPochhammer_ne_zero [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (b d : ℕ) (hb : 0 < b) :
    specializationPochhammer q t b d ≠ 0 := by
  rw [specializationPochhammer, Finset.prod_ne_zero_iff]
  intro a _
  exact specializationBinomial_ne_zero hqt a b hb

/-- The principal specialization is nonzero at power-pair injective parameters. -/
theorem principalSpecialization_ne_zero [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (lam : Nat.PartitionVector N) :
    principalSpecialization q t lam ≠ 0 := by
  rw [principalSpecialization]
  apply mul_ne_zero (pow_ne_zero _ hqt.ne_zero.2)
  rw [Finset.prod_ne_zero_iff]
  intro ij hij
  rw [principalRowFactor]
  apply div_ne_zero
  · exact specializationPochhammer_ne_zero hqt _ _ (by positivity)
  · exact specializationPochhammer_ne_zero hqt _ _
      (Nat.sub_pos_of_lt (by simpa using hij))

private theorem rowDifference_increment_of_notMem_of_notMem
    (mu : Nat.PartitionVector N) (I : Finset (Fin N)) (hI : IsLegal mu I)
    (ij : Fin N × Fin N) (hi : ij.1 ∉ I) (hj : ij.2 ∉ I) :
    Nat.PartitionVector.Pieri.rowDifference (incrementPartition mu I hI) ij =
      Nat.PartitionVector.Pieri.rowDifference mu ij := by
  simp [Nat.PartitionVector.Pieri.rowDifference, hi, hj]

private theorem rowDifference_increment_of_mem_of_mem
    (mu : Nat.PartitionVector N) (I : Finset (Fin N)) (hI : IsLegal mu I)
    (ij : Fin N × Fin N) (hi : ij.1 ∈ I) (hj : ij.2 ∈ I) :
    Nat.PartitionVector.Pieri.rowDifference (incrementPartition mu I hI) ij =
      Nat.PartitionVector.Pieri.rowDifference mu ij := by
  simp [Nat.PartitionVector.Pieri.rowDifference, hi, hj]

private theorem rowDifference_increment_of_mem_of_notMem
    (mu : Nat.PartitionVector N) (I : Finset (Fin N)) (hI : IsLegal mu I)
    (ij : Fin N × Fin N) (hij : ij.1 ≤ ij.2) (hi : ij.1 ∈ I) (hj : ij.2 ∉ I) :
    Nat.PartitionVector.Pieri.rowDifference (incrementPartition mu I hI) ij =
      Nat.PartitionVector.Pieri.rowDifference mu ij + 1 := by
  have hmu := mu.antitone hij
  simp only [Nat.PartitionVector.Pieri.rowDifference, incrementPartition_apply, hi, hj,
    ↓reduceIte]
  lia

private theorem rowDifference_increment_of_notMem_of_mem
    (mu : Nat.PartitionVector N) (I : Finset (Fin N)) (hI : IsLegal mu I)
    (ij : Fin N × Fin N) (hij : ij.1 ≤ ij.2) (hi : ij.1 ∉ I) (hj : ij.2 ∈ I) :
    Nat.PartitionVector.Pieri.rowDifference (incrementPartition mu I hI) ij =
      Nat.PartitionVector.Pieri.rowDifference mu ij - 1 := by
  have hlegal := hI hij
  simp only [increment, hi, hj, ↓reduceIte] at hlegal
  simp only [Nat.PartitionVector.Pieri.rowDifference, incrementPartition_apply, hi, hj,
    ↓reduceIte]
  lia

private theorem rowDifference_pos_of_notMem_of_mem
    (mu : Nat.PartitionVector N) (I : Finset (Fin N)) (hI : IsLegal mu I)
    (ij : Fin N × Fin N) (hij : ij.1 ≤ ij.2) (hi : ij.1 ∉ I) (hj : ij.2 ∈ I) :
    0 < Nat.PartitionVector.Pieri.rowDifference mu ij := by
  have hlegal := hI hij
  simp only [increment, hi, hj, ↓reduceIte] at hlegal
  exact Nat.sub_pos_of_lt hlegal

private theorem principalRowFactor_increment_of_same [Field K] (q t : K)
    (mu : Nat.PartitionVector N) (I : Finset (Fin N)) (hI : IsLegal mu I)
    (ij : Fin N × Fin N)
    (hsame : ij.1 ∈ I ↔ ij.2 ∈ I) :
    principalRowFactor q t (incrementPartition mu I hI) ij =
      principalRowFactor q t mu ij := by
  by_cases hi : ij.1 ∈ I
  · exact congrArg₂ (fun a b ↦ a / b)
      (congrArg (specializationPochhammer q t
        (Nat.PartitionVector.Pieri.rowDistance ij + 1))
        (rowDifference_increment_of_mem_of_mem mu I hI ij hi (hsame.mp hi)))
      (congrArg (specializationPochhammer q t
        (Nat.PartitionVector.Pieri.rowDistance ij))
        (rowDifference_increment_of_mem_of_mem mu I hI ij hi (hsame.mp hi)))
  · have hj : ij.2 ∉ I := fun h ↦ hi (hsame.mpr h)
    rw [principalRowFactor, principalRowFactor,
      rowDifference_increment_of_notMem_of_notMem mu I hI ij hi hj]

private theorem principalRowFactor_increment_of_mem_of_notMem [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (mu : Nat.PartitionVector N)
    (I : Finset (Fin N)) (hI : IsLegal mu I) (ij : Fin N × Fin N)
    (hij : ij.1 < ij.2) (hi : ij.1 ∈ I) (hj : ij.2 ∉ I) :
    specializationBinomial q t (Nat.PartitionVector.Pieri.rowDifference mu ij)
        (Nat.PartitionVector.Pieri.rowDistance ij + 1) /
        specializationBinomial q t (Nat.PartitionVector.Pieri.rowDifference mu ij)
          (Nat.PartitionVector.Pieri.rowDistance ij) *
      principalRowFactor q t mu ij =
        principalRowFactor q t (incrementPartition mu I hI) ij := by
  let d := Nat.PartitionVector.Pieri.rowDifference mu ij
  let m := Nat.PartitionVector.Pieri.rowDistance ij
  have hm : 0 < m := Nat.sub_pos_of_lt hij
  have hdiff :
      Nat.PartitionVector.Pieri.rowDifference (incrementPartition mu I hI) ij = d + 1 :=
    rowDifference_increment_of_mem_of_notMem mu I hI ij (Fin.le_of_lt hij) hi hj
  have hdm : specializationBinomial q t d m ≠ 0 :=
    specializationBinomial_ne_zero hqt d m hm
  have hp0 : specializationPochhammer q t m d ≠ 0 :=
    specializationPochhammer_ne_zero hqt m d hm
  have hp1 : specializationPochhammer q t (m + 1) d ≠ 0 :=
    specializationPochhammer_ne_zero hqt (m + 1) d (by positivity)
  rw [principalRowFactor, principalRowFactor, hdiff,
    specializationPochhammer_succ, specializationPochhammer_succ]
  field_simp
  ring

private theorem principalRowFactor_increment_of_notMem_of_mem [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (mu : Nat.PartitionVector N)
    (I : Finset (Fin N)) (hI : IsLegal mu I) (ij : Fin N × Fin N)
    (hij : ij.1 < ij.2) (hi : ij.1 ∉ I) (hj : ij.2 ∈ I) :
    specializationBinomial q t (Nat.PartitionVector.Pieri.rowDifference mu ij)
        (Nat.PartitionVector.Pieri.rowDistance ij - 1) /
        specializationBinomial q t (Nat.PartitionVector.Pieri.rowDifference mu ij)
          (Nat.PartitionVector.Pieri.rowDistance ij) *
        principalRowFactor q t mu ij /
      principalRowFactor q t (incrementPartition mu I hI) ij =
        Nat.PartitionVector.Pieri.pairNum mu q t ij /
          Nat.PartitionVector.Pieri.pairDen mu q t ij := by
  let d := Nat.PartitionVector.Pieri.rowDifference mu ij
  let m := Nat.PartitionVector.Pieri.rowDistance ij
  have hm : 0 < m := Nat.sub_pos_of_lt hij
  have hd : 0 < d :=
    rowDifference_pos_of_notMem_of_mem mu I hI ij (Fin.le_of_lt hij) hi hj
  have hdiff :
      Nat.PartitionVector.Pieri.rowDifference (incrementPartition mu I hI) ij = d - 1 :=
    rowDifference_increment_of_notMem_of_mem mu I hI ij (Fin.le_of_lt hij) hi hj
  have hdsucc : d - 1 + 1 = d := by lia
  have hdm : specializationBinomial q t d m ≠ 0 :=
    specializationBinomial_ne_zero hqt d m hm
  have hdmm : specializationBinomial q t d (m - 1) ≠ 0 :=
    specializationBinomial_ne_zero_of_ne hqt d (m - 1) (by simp [hd.ne'])
  have hdp : specializationBinomial q t (d - 1) m ≠ 0 :=
    specializationBinomial_ne_zero hqt (d - 1) m hm
  have hp0 : specializationPochhammer q t m (d - 1) ≠ 0 :=
    specializationPochhammer_ne_zero hqt m (d - 1) hm
  have hp1 : specializationPochhammer q t (m + 1) (d - 1) ≠ 0 :=
    specializationPochhammer_ne_zero hqt (m + 1) (d - 1) (by positivity)
  have hpoch0 :
      specializationPochhammer q t m d =
        specializationPochhammer q t m (d - 1) *
          specializationBinomial q t (d - 1) m := by
    conv_lhs => rw [← hdsucc]
    exact specializationPochhammer_succ q t m (d - 1)
  have hpoch1 :
      specializationPochhammer q t (m + 1) d =
        specializationPochhammer q t (m + 1) (d - 1) *
          specializationBinomial q t (d - 1) (m + 1) := by
    conv_lhs => rw [← hdsucc]
    exact specializationPochhammer_succ q t (m + 1) (d - 1)
  rw [principalRowFactor, principalRowFactor, hdiff]
  change specializationBinomial q t d (m - 1) / specializationBinomial q t d m *
      (specializationPochhammer q t (m + 1) d /
        specializationPochhammer q t m d) /
      (specializationPochhammer q t (m + 1) (d - 1) /
        specializationPochhammer q t m (d - 1)) = _
  rw [hpoch0, hpoch1]
  change _ =
    (specializationBinomial q t d (m - 1) *
      specializationBinomial q t (d - 1) (m + 1)) /
      (specializationBinomial q t d m * specializationBinomial q t (d - 1) m)
  field_simp

private theorem grid_eq_mul_grid_of_lt [Field K] (q t : K)
    (mu : Nat.PartitionVector N) {i j : Fin N} (hij : i < j) :
    grid q t mu i =
      q ^ Nat.PartitionVector.Pieri.rowDifference mu (i, j) *
        t ^ Nat.PartitionVector.Pieri.rowDistance (i, j) * grid q t mu j := by
  have hmu : mu j ≤ mu i := mu.antitone (Fin.le_of_lt hij)
  have hmu' : mu j + Nat.PartitionVector.Pieri.rowDifference mu (i, j) = mu i := by
    simp only [Nat.PartitionVector.Pieri.rowDifference]
    lia
  have hrev :
      j.rev.val + Nat.PartitionVector.Pieri.rowDistance (i, j) = i.rev.val := by
    simp only [Nat.PartitionVector.Pieri.rowDistance, Fin.val_rev]
    lia
  rw [grid, grid, ← hmu', ← hrev, pow_add, pow_add]
  ring

private theorem gridFactor_of_lt [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (mu : Nat.PartitionVector N)
    {i j : Fin N} (hij : i < j) :
    gridFactor q t mu i j =
      specializationBinomial q t
          (Nat.PartitionVector.Pieri.rowDifference mu (i, j))
          (Nat.PartitionVector.Pieri.rowDistance (i, j) + 1) /
        specializationBinomial q t
          (Nat.PartitionVector.Pieri.rowDifference mu (i, j))
          (Nat.PartitionVector.Pieri.rowDistance (i, j)) := by
  let d := Nat.PartitionVector.Pieri.rowDifference mu (i, j)
  let m := Nat.PartitionVector.Pieri.rowDistance (i, j)
  have hm : 0 < m := Nat.sub_pos_of_lt hij
  have hx : grid q t mu j ≠ 0 := by
    rw [grid]
    exact mul_ne_zero (pow_ne_zero _ hqt.ne_zero.1) (pow_ne_zero _ hqt.ne_zero.2)
  have hden : specializationBinomial q t d m ≠ 0 :=
    specializationBinomial_ne_zero hqt d m hm
  have hraw : 1 - q ^ d * t ^ m ≠ 0 := by
    simpa [specializationBinomial] using hden
  have hleft : q ^ d * t ^ m * grid q t mu j - grid q t mu j ≠ 0 := by
    have ha : q ^ d * t ^ m - 1 ≠ 0 := by
      rw [show q ^ d * t ^ m - 1 = -(1 - q ^ d * t ^ m) by ring]
      exact neg_ne_zero.mpr hraw
    convert mul_ne_zero ha hx using 1
    ring
  rw [gridFactor, numeratorFactor, grid_eq_mul_grid_of_lt q t mu hij]
  change (t * (q ^ d * t ^ m * grid q t mu j) - grid q t mu j) /
      (q ^ d * t ^ m * grid q t mu j - grid q t mu j) =
        (1 - q ^ d * t ^ (m + 1)) / (1 - q ^ d * t ^ m)
  rw [pow_succ]
  apply (div_eq_div_iff hleft hraw).2
  ring

private theorem gridFactor_reverse_of_lt [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (mu : Nat.PartitionVector N)
    {i j : Fin N} (hij : i < j) :
    gridFactor q t mu j i =
      t * specializationBinomial q t
          (Nat.PartitionVector.Pieri.rowDifference mu (i, j))
          (Nat.PartitionVector.Pieri.rowDistance (i, j) - 1) /
        specializationBinomial q t
          (Nat.PartitionVector.Pieri.rowDifference mu (i, j))
          (Nat.PartitionVector.Pieri.rowDistance (i, j)) := by
  let d := Nat.PartitionVector.Pieri.rowDifference mu (i, j)
  let m := Nat.PartitionVector.Pieri.rowDistance (i, j)
  have hm : 0 < m := Nat.sub_pos_of_lt hij
  have hmsucc : m - 1 + 1 = m := by lia
  have hx : grid q t mu j ≠ 0 := by
    rw [grid]
    exact mul_ne_zero (pow_ne_zero _ hqt.ne_zero.1) (pow_ne_zero _ hqt.ne_zero.2)
  have hden : specializationBinomial q t d m ≠ 0 :=
    specializationBinomial_ne_zero hqt d m hm
  have hpow : t ^ m = t ^ (m - 1) * t := by
    conv_lhs => rw [← hmsucc, pow_add, pow_one]
  rw [gridFactor, numeratorFactor, grid_eq_mul_grid_of_lt q t mu hij]
  change (t * grid q t mu j - q ^ d * t ^ m * grid q t mu j) /
      (grid q t mu j - q ^ d * t ^ m * grid q t mu j) =
        t * (1 - q ^ d * t ^ (m - 1)) / (1 - q ^ d * t ^ m)
  rw [hpow]
  field_simp

private theorem card_product_filter_lt_eq_sum [LinearOrder α]
    (s t : Finset α) :
    ((s ×ˢ t).filter fun ij ↦ ij.1 < ij.2).card =
      ∑ j ∈ t, (s.filter fun i ↦ i < j).card := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      have heq :
          ((s ×ˢ insert a t).filter fun ij ↦ ij.1 < ij.2) =
            ((s ×ˢ {a}).filter fun ij ↦ ij.1 < ij.2) ∪
              ((s ×ˢ t).filter fun ij ↦ ij.1 < ij.2) := by
        ext ij
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
          Finset.mem_union, Finset.mem_singleton]
        grind
      have hdisj :
          Disjoint ((s ×ˢ {a}).filter fun ij ↦ ij.1 < ij.2)
            ((s ×ˢ t).filter fun ij ↦ ij.1 < ij.2) := by
        rw [Finset.disjoint_left]
        intro ij hja hjt
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hja hjt
        exact ha (hja.1.2 ▸ hjt.1.2)
      have hfirst :
          ((s ×ˢ {a}).filter fun ij ↦ ij.1 < ij.2).card =
            (s.filter fun i ↦ i < a).card := by
        have hfirstset :
            ((s ×ˢ {a}).filter fun ij ↦ ij.1 < ij.2) =
              (s.filter fun i ↦ i < a) ×ˢ {a} := by
          ext ij
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
          grind
        rw [hfirstset, Finset.card_product]
        simp
      rw [heq, Finset.card_union_of_disjoint hdisj, hfirst, ih, Finset.sum_insert ha]

private def lowerCrossPairs (I : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  (orderedRowPairs N).filter fun ij ↦ ij.1 ∉ I ∧ ij.2 ∈ I

private theorem sum_val_eq_choose_add_card_lowerCrossPairs (I : Finset (Fin N)) :
    ∑ i ∈ I, i.val = I.card.choose 2 + (lowerCrossPairs I).card := by
  classical
  have hsplit (i : Fin N) :
      i.val = (I.filter fun j ↦ j < i).card +
        ((Finset.univ \ I).filter fun j ↦ j < i).card := by
    have hcard : (Finset.univ.filter fun j : Fin N ↦ j < i).card = i.val := by
      rw [show Finset.univ.filter (fun j : Fin N ↦ j < i) = Finset.Iio i by
        ext j
        simp]
      exact Fin.card_Iio i
    rw [← hcard]
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun j : Fin N ↦ j < i) (fun j ↦ j ∈ I)
    rw [← hpartition]
    have hleft :
        (Finset.univ.filter fun j : Fin N ↦ j < i).filter (fun j ↦ j ∈ I) =
          I.filter fun j ↦ j < i := by
      ext j
      simp [and_comm]
    have hright :
        (Finset.univ.filter fun j : Fin N ↦ j < i).filter (fun j ↦ j ∉ I) =
          (Finset.univ \ I).filter fun j ↦ j < i := by
      ext j
      simp [and_comm]
    rw [hleft, hright]
  calc
    ∑ i ∈ I, i.val =
        ∑ i ∈ I, ((I.filter fun j ↦ j < i).card +
          ((Finset.univ \ I).filter fun j ↦ j < i).card) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hsplit i
    _ = (∑ i ∈ I, (I.filter fun j ↦ j < i).card) +
        ∑ i ∈ I, ((Finset.univ \ I).filter fun j ↦ j < i).card := by
      rw [Finset.sum_add_distrib]
    _ = I.card.choose 2 + (lowerCrossPairs I).card := by
      rw [← card_product_filter_lt_eq_sum I I,
        Finset.card_product_filter_lt,
        ← card_product_filter_lt_eq_sum (Finset.univ \ I) I]
      have heq :
          ((Finset.univ \ I) ×ˢ I).filter (fun ij ↦ ij.1 < ij.2) =
            lowerCrossPairs I := by
        unfold lowerCrossPairs orderedRowPairs
        ext ij
        simp [and_comm]
      rw [heq]

/-- Incrementing a legal row set increases `n(lambda)` by the sum of its row indices. -/
theorem nStatistic_incrementPartition (mu : Nat.PartitionVector N)
    (I : Finset (Fin N)) (hI : IsLegal mu I) :
    nStatistic (incrementPartition mu I hI) =
      nStatistic mu + ∑ i ∈ I, i.val := by
  rw [nStatistic, nStatistic]
  simp_rw [incrementPartition_apply, Nat.mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext i
    simp
  · intro i _
    simp

private def localRatio [Field K] (q t : K) (mu : Nat.PartitionVector N)
    (I : Finset (Fin N)) (ij : Fin N × Fin N) : K :=
  if ij.1 ∈ I then
    if ij.2 ∈ I then 1 else
      specializationBinomial q t (Nat.PartitionVector.Pieri.rowDifference mu ij)
          (Nat.PartitionVector.Pieri.rowDistance ij + 1) /
        specializationBinomial q t (Nat.PartitionVector.Pieri.rowDifference mu ij)
          (Nat.PartitionVector.Pieri.rowDistance ij)
  else if ij.2 ∈ I then
    specializationBinomial q t (Nat.PartitionVector.Pieri.rowDifference mu ij)
        (Nat.PartitionVector.Pieri.rowDistance ij - 1) /
      specializationBinomial q t (Nat.PartitionVector.Pieri.rowDifference mu ij)
        (Nat.PartitionVector.Pieri.rowDistance ij)
  else 1

private theorem prod_orderedRowPairs_cross [CommMonoid K] (I : Finset (Fin N))
    (f : Fin N → Fin N → K) :
    (∏ ij ∈ (orderedRowPairs N).filter
      (fun ij ↦ (ij.1 ∈ I ∧ ij.2 ∉ I) ∨ (ij.1 ∉ I ∧ ij.2 ∈ I)),
      if ij.1 ∈ I then f ij.1 ij.2 else f ij.2 ij.1) =
      ∏ i ∈ I, ∏ j ∈ Finset.univ \ I, f i j := by
  classical
  rw [← Finset.prod_product']
  apply Finset.prod_bij
    (fun ij _ ↦ if ij.1 ∈ I then ij else (ij.2, ij.1))
  · intro ij hij
    simp only [Finset.mem_filter] at hij
    rcases hij.2 with h | h
    · simp [h.1, h.2]
    · simp [h.1, h.2]
  · intro a ha b hb hab
    simp only [Finset.mem_filter] at ha hb
    have halt : a.1 < a.2 := by simpa using ha.1
    have hblt : b.1 < b.2 := by simpa using hb.1
    by_cases hai : a.1 ∈ I <;> by_cases hbi : b.1 ∈ I
    · simpa only [hai, hbi, ↓reduceIte] using hab
    · simp only [hai, hbi, ↓reduceIte] at hab
      have hreverse : a.2 < a.1 := by
        have hfst : a.1 = b.2 := congrArg Prod.fst hab
        have hsnd : a.2 = b.1 := congrArg Prod.snd hab
        rw [hsnd, hfst]
        exact hblt
      exact (lt_asymm halt hreverse).elim
    · simp only [hai, hbi, ↓reduceIte] at hab
      have hreverse : a.2 < a.1 := by
        have hfst : a.2 = b.1 := congrArg Prod.fst hab
        have hsnd : a.1 = b.2 := congrArg Prod.snd hab
        rw [hfst, hsnd]
        exact hblt
      exact (lt_asymm halt hreverse).elim
    · simp only [hai, hbi, ↓reduceIte] at hab
      exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
  · intro b hb
    simp only [Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ, true_and] at hb
    by_cases hlt : b.1 < b.2
    · refine ⟨b, ?_, ?_⟩
      · simp [hlt, hb.1, hb.2]
      · simp [hb.1]
    · have hne : b.1 ≠ b.2 := by
        intro h
        exact hb.2 (h ▸ hb.1)
      have hgt : b.2 < b.1 := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
      refine ⟨(b.2, b.1), ?_, ?_⟩
      · simp [hgt, hb.1, hb.2]
      · simp [hb.2]
  · intro a ha
    simp only [Finset.mem_filter] at ha
    by_cases hai : a.1 ∈ I
    · simp [hai]
    · simp [hai]

private theorem gridCoefficient_eq_pow_sum_mul_prod_localRatio [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (mu : Nat.PartitionVector N)
    (I : Finset (Fin N)) :
    B q t mu I =
      t ^ (∑ i ∈ I, i.val) *
        ∏ ij ∈ orderedRowPairs N, localRatio q t mu I ij := by
  classical
  rw [B, gridCoefficient]
  rw [← prod_orderedRowPairs_cross I (gridFactor q t mu)]
  have hpoint (ij : Fin N × Fin N) (hij : ij ∈ orderedRowPairs N) :
      (if (ij.1 ∈ I ∧ ij.2 ∉ I) ∨ (ij.1 ∉ I ∧ ij.2 ∈ I) then
          if ij.1 ∈ I then gridFactor q t mu ij.1 ij.2
          else gridFactor q t mu ij.2 ij.1
        else 1) =
      (if ij ∈ lowerCrossPairs I then t else 1) * localRatio q t mu I ij := by
    have hlt : ij.1 < ij.2 := by simpa using hij
    by_cases hi : ij.1 ∈ I <;> by_cases hj : ij.2 ∈ I
    · simp [localRatio, lowerCrossPairs, hi, hj]
    · simp only [hi, hj, true_and, not_false_eq_true, and_false, or_false,
        ↓reduceIte, localRatio]
      rw [gridFactor_of_lt hqt mu hlt]
      simp [lowerCrossPairs, hij, hi, hj]
    · simp only [hi, hj, false_and, not_false_eq_true, true_and, or_true, ↓reduceIte,
        localRatio]
      rw [gridFactor_reverse_of_lt hqt mu hlt]
      simp [lowerCrossPairs, hij, hi, hj]
      ring
    · simp [localRatio, lowerCrossPairs, hi, hj]
  rw [Finset.prod_filter]
  have hprod := Finset.prod_congr rfl hpoint
  rw [hprod, Finset.prod_mul_distrib]
  rw [← Finset.prod_filter, Finset.prod_const]
  have hfilter :
      (orderedRowPairs N).filter (fun ij ↦ ij ∈ lowerCrossPairs I) =
        lowerCrossPairs I := by
    ext ij
    simp [lowerCrossPairs]
  rw [hfilter, ← mul_assoc, ← pow_add,
    sum_val_eq_choose_add_card_lowerCrossPairs I]
  rw [Nat.choose_two_right]

private theorem principalRowFactor_ne_zero [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (lam : Nat.PartitionVector N)
    {ij : Fin N × Fin N} (hij : ij ∈ orderedRowPairs N) :
    principalRowFactor q t lam ij ≠ 0 := by
  rw [principalRowFactor]
  apply div_ne_zero
  · exact specializationPochhammer_ne_zero hqt _ _ (by positivity)
  · exact specializationPochhammer_ne_zero hqt _ _
      (Nat.sub_pos_of_lt (by simpa using hij))

private theorem localRatio_mul_rowFactor_div_increment [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (mu : Nat.PartitionVector N)
    (I : Finset (Fin N)) (hI : IsLegal mu I)
    (ij : Fin N × Fin N) (hij : ij ∈ orderedRowPairs N) :
    localRatio q t mu I ij * principalRowFactor q t mu ij /
        principalRowFactor q t (incrementPartition mu I hI) ij =
      if ij ∈ Nat.PartitionVector.Pieri.rowPairs (stripOfFinset I) then
        Nat.PartitionVector.Pieri.pairNum mu q t ij /
          Nat.PartitionVector.Pieri.pairDen mu q t ij
      else 1 := by
  have hlt : ij.1 < ij.2 := by simpa using hij
  by_cases hi : ij.1 ∈ I <;> by_cases hj : ij.2 ∈ I
  · rw [principalRowFactor_increment_of_same q t mu I hI ij (by simp [hi, hj])]
    simp [localRatio, stripOfFinset, hi, hj, principalRowFactor_ne_zero hqt mu hij]
  · have hchange := principalRowFactor_increment_of_mem_of_notMem
      hqt mu I hI ij hlt hi hj
    simp only [localRatio, hi, hj, ↓reduceIte]
    rw [hchange]
    simp [Nat.PartitionVector.Pieri.mem_rowPairs, stripOfFinset, hlt, hi, hj,
      principalRowFactor_ne_zero hqt (incrementPartition mu I hI) hij]
  · have hchange := principalRowFactor_increment_of_notMem_of_mem
      hqt mu I hI ij hlt hi hj
    simpa [localRatio, Nat.PartitionVector.Pieri.mem_rowPairs, stripOfFinset,
      hlt, hi, hj] using hchange
  · rw [principalRowFactor_increment_of_same q t mu I hI ij (by simp [hi, hj])]
    simp [localRatio, stripOfFinset, hi, hj, principalRowFactor_ne_zero hqt mu hij]

/-- Cancellation of the row principal specialization against the grid coefficient leaves the
row-pair vertical Pieri coefficient. -/
theorem principalSpecialization_pieriCancellation [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (mu : Nat.PartitionVector N)
    (I : Finset (Fin N)) (hI : IsLegal mu I) :
    B q t mu I * principalSpecialization q t mu /
        principalSpecialization q t (incrementPartition mu I hI) =
      Nat.PartitionVector.Pieri.pieriNum mu (stripOfFinset I) q t /
        Nat.PartitionVector.Pieri.pieriDen mu (stripOfFinset I) q t := by
  classical
  let lam := incrementPartition mu I hI
  let s := ∑ i ∈ I, i.val
  have hprod :
      (∏ ij ∈ orderedRowPairs N,
        localRatio q t mu I ij * principalRowFactor q t mu ij /
          principalRowFactor q t lam ij) =
        Nat.PartitionVector.Pieri.pieriNum mu (stripOfFinset I) q t /
          Nat.PartitionVector.Pieri.pieriDen mu (stripOfFinset I) q t := by
    calc
      (∏ ij ∈ orderedRowPairs N,
          localRatio q t mu I ij * principalRowFactor q t mu ij /
            principalRowFactor q t lam ij) =
          ∏ ij ∈ orderedRowPairs N,
            if ij ∈ Nat.PartitionVector.Pieri.rowPairs (stripOfFinset I) then
              Nat.PartitionVector.Pieri.pairNum mu q t ij /
                Nat.PartitionVector.Pieri.pairDen mu q t ij
            else 1 := by
        apply Finset.prod_congr rfl
        intro ij hij
        exact localRatio_mul_rowFactor_div_increment hqt mu I hI ij hij
      _ = ∏ ij ∈ Nat.PartitionVector.Pieri.rowPairs (stripOfFinset I),
          Nat.PartitionVector.Pieri.pairNum mu q t ij /
            Nat.PartitionVector.Pieri.pairDen mu q t ij := by
        rw [← Finset.prod_filter]
        congr 1
        ext ij
        simp [Nat.PartitionVector.Pieri.mem_rowPairs]
      _ = _ := by
        rw [Finset.prod_div_distrib]
        rfl
  rw [← hprod, gridCoefficient_eq_pow_sum_mul_prod_localRatio hqt mu I]
  rw [principalSpecialization, principalSpecialization]
  change
    (t ^ s * ∏ ij ∈ orderedRowPairs N, localRatio q t mu I ij) *
        (t ^ nStatistic mu *
          ∏ ij ∈ orderedRowPairs N, principalRowFactor q t mu ij) /
      (t ^ nStatistic lam *
        ∏ ij ∈ orderedRowPairs N, principalRowFactor q t lam ij) = _
  have hn : nStatistic lam = nStatistic mu + s :=
    nStatistic_incrementPartition mu I hI
  rw [hn, pow_add]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
  have ht : t ≠ 0 := hqt.ne_zero.2
  have hnew :
      (∏ ij ∈ orderedRowPairs N, principalRowFactor q t lam ij) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro ij hij
    exact principalRowFactor_ne_zero hqt lam hij
  field_simp

/-- The Pieri row-pair set of an initial row segment is empty. -/
theorem rowPairs_stripOfFinset_prefixRows (N r : ℕ) :
    Nat.PartitionVector.Pieri.rowPairs (stripOfFinset (prefixRows N r)) = ∅ := by
  ext ij
  simp only [Nat.PartitionVector.Pieri.mem_rowPairs, Finset.notMem_empty, iff_false]
  intro h
  have hi : ij.1 ∈ prefixRows N r := by
    rw [mem_prefixRows]
    have hj : ij.2.val < r := by
      rw [← mem_prefixRows]
      exact (stripOfFinset_eq_one_iff (prefixRows N r) ij.2).mp h.2.2
    exact lt_trans h.1 hj
  have hni : ij.1 ∉ prefixRows N r :=
    (stripOfFinset_eq_zero_iff (prefixRows N r) ij.1).mp h.2.1
  exact hni hi

/-- Adding one to an initial segment multiplies the row principal specialization by the
corresponding grid coefficient. -/
theorem principalSpecialization_incrementPrefix [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (mu : Nat.PartitionVector N) (r : ℕ) :
    principalSpecialization q t (incrementPrefix mu r) =
      B q t mu (prefixRows N r) * principalSpecialization q t mu := by
  have hcancel := principalSpecialization_pieriCancellation hqt mu
    (prefixRows N r) (isLegal_prefixRows mu r)
  simp only [Nat.PartitionVector.Pieri.pieriNum, Nat.PartitionVector.Pieri.pieriDen,
    rowPairs_stripOfFinset_prefixRows, Finset.prod_empty, one_div] at hcancel
  have hcancel' :
      B q t mu (prefixRows N r) * principalSpecialization q t mu /
          principalSpecialization q t (incrementPrefix mu r) = 1 := by
    simpa [incrementPrefix] using hcancel
  have hne : principalSpecialization q t (incrementPrefix mu r) ≠ 0 :=
    principalSpecialization_ne_zero hqt (incrementPrefix mu r)
  exact ((div_eq_one_iff_eq hne).mp hcancel').symm

end Nat.PartitionVector.Macdonald
