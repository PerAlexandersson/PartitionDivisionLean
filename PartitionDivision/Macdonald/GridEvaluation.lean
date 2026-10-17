/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Mathlib.Combinatorics.Enumerative.Partition.Restricted
public import PartitionDivision.Mathlib.RingTheory.MvPolynomial.Antisymmetric
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Evaluation of Macdonald difference-operator coefficients on a partition grid

This file evaluates the rational coefficient attached to a subset of rows at the grid
`x_i = q^(mu_i) t^(N - 1 - i)`.  Distinctness of the Laurent monomials in `q` and `t` is isolated
as `PowerPairInjective`; the canonical generators of the fraction field of a bivariate
polynomial ring satisfy this condition.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Nat.PartitionVector.Macdonald

variable {N : ℕ} {K : Type*}

/-- Distinct pairs of natural exponents give distinct products of powers of `q` and `t`. -/
def PowerPairInjective [Monoid K] (q t : K) : Prop :=
  Function.Injective fun ab : ℕ × ℕ ↦ q ^ ab.1 * t ^ ab.2

/-- The two variables remain power-pair injective in the fraction field of the bivariate
polynomial ring. -/
theorem powerPairInjective_fractionRing :
    PowerPairInjective
      (algebraMap (MvPolynomial (Fin 2) ℚ)
        (FractionRing (MvPolynomial (Fin 2) ℚ)) (MvPolynomial.X 0))
      (algebraMap (MvPolynomial (Fin 2) ℚ)
        (FractionRing (MvPolynomial (Fin 2) ℚ)) (MvPolynomial.X 1)) := by
  intro ab cd h
  apply Prod.ext
  · have hpoly :
        MvPolynomial.X (R := ℚ) (0 : Fin 2) ^ ab.1 * MvPolynomial.X 1 ^ ab.2 =
          MvPolynomial.X 0 ^ cd.1 * MvPolynomial.X 1 ^ cd.2 := by
      apply IsFractionRing.injective (MvPolynomial (Fin 2) ℚ)
        (FractionRing (MvPolynomial (Fin 2) ℚ))
      simpa only [map_mul, map_pow] using h
    simp only [MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial] at hpoly
    have hexp :
        Finsupp.single (0 : Fin 2) ab.1 + Finsupp.single 1 ab.2 =
          Finsupp.single 0 cd.1 + Finsupp.single 1 cd.2 := by
      simpa only [MvPolynomial.monomial_eq_monomial_iff, one_mul, one_ne_zero,
        and_true, false_and, or_false] using hpoly
    have := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 0) hexp
    simpa using this
  · have hpoly :
        MvPolynomial.X (R := ℚ) (0 : Fin 2) ^ ab.1 * MvPolynomial.X 1 ^ ab.2 =
          MvPolynomial.X 0 ^ cd.1 * MvPolynomial.X 1 ^ cd.2 := by
      apply IsFractionRing.injective (MvPolynomial (Fin 2) ℚ)
        (FractionRing (MvPolynomial (Fin 2) ℚ))
      simpa only [map_mul, map_pow] using h
    simp only [MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.monomial_mul_monomial] at hpoly
    have hexp :
        Finsupp.single (0 : Fin 2) ab.1 + Finsupp.single 1 ab.2 =
          Finsupp.single 0 cd.1 + Finsupp.single 1 cd.2 := by
      simpa only [MvPolynomial.monomial_eq_monomial_iff, one_mul, one_ne_zero,
        and_true, false_and, or_false] using hpoly
    have := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 1) hexp
    simpa using this

/-- The Macdonald evaluation grid attached to a partition vector. -/
def grid [Monoid K] (q t : K) (mu : Nat.PartitionVector N) (i : Fin N) : K :=
  q ^ mu i * t ^ i.rev.val

/-- Add one to precisely the coordinates in `I`. -/
def increment (mu : Nat.PartitionVector N) (I : Finset (Fin N)) (i : Fin N) : ℕ :=
  mu i + if i ∈ I then 1 else 0

/-- A subset of rows is legal when its coordinatewise increment remains antitone. -/
def IsLegal (mu : Nat.PartitionVector N) (I : Finset (Fin N)) : Prop :=
  Antitone (increment mu I)

/-- The incremented partition vector associated to a legal subset of rows. -/
def incrementPartition (mu : Nat.PartitionVector N) (I : Finset (Fin N))
    (hI : IsLegal mu I) : Nat.PartitionVector N :=
  ⟨increment mu I, hI⟩

/-- Evaluation of an incremented partition vector. -/
@[simp]
theorem incrementPartition_apply (mu : Nat.PartitionVector N) (I : Finset (Fin N))
    (hI : IsLegal mu I) (i : Fin N) :
    incrementPartition mu I hI i = mu i + if i ∈ I then 1 else 0 := rfl

/-- The two parameters of a power-pair injective pair are nonzero. -/
theorem PowerPairInjective.ne_zero [MonoidWithZero K] {q t : K}
    (hqt : PowerPairInjective q t) : q ≠ 0 ∧ t ≠ 0 := by
  constructor
  · intro hq
    have h := hqt (a₁ := (1, 1)) (a₂ := (2, 1)) (by simp [hq])
    norm_num at h
  · intro ht
    have h := hqt (a₁ := (1, 1)) (a₂ := (1, 2)) (by simp [ht])
    norm_num at h

/-- Distinct rows give distinct points on a power-pair injective grid. -/
theorem grid_ne_of_ne [Monoid K] {q t : K} (hqt : PowerPairInjective q t)
    (mu : Nat.PartitionVector N) {i j : Fin N} (hij : i ≠ j) :
    grid q t mu i ≠ grid q t mu j := by
  intro h
  have hexp := hqt (a₁ := (mu i, i.rev.val)) (a₂ := (mu j, j.rev.val)) (by
    simpa only [grid] using h)
  apply hij
  apply Fin.rev_injective
  exact Fin.ext (congrArg Prod.snd hexp)

/-- Every denominator in the grid coefficient is nonzero. -/
theorem grid_sub_ne_zero [Field K] {q t : K} (hqt : PowerPairInjective q t)
    (mu : Nat.PartitionVector N) {i j : Fin N} (hij : i ≠ j) :
    grid q t mu i - grid q t mu j ≠ 0 :=
  sub_ne_zero.mpr (grid_ne_of_ne hqt mu hij)

/-- A numerator factor in the grid coefficient. -/
def numeratorFactor [Ring K] (q t : K) (mu : Nat.PartitionVector N)
    (i j : Fin N) : K :=
  t * grid q t mu i - grid q t mu j

/-- A numerator factor vanishes exactly at an adjacent equal pair whose lower row is shifted. -/
theorem numeratorFactor_eq_zero_iff [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (mu : Nat.PartitionVector N) (i j : Fin N) :
    numeratorFactor q t mu i j = 0 ↔ mu i = mu j ∧ j.val + 1 = i.val := by
  rw [numeratorFactor, sub_eq_zero]
  have hrewrite :
      t * grid q t mu i = q ^ mu i * t ^ (i.rev.val + 1) := by
    simp only [grid, pow_succ]
    ring
  rw [hrewrite]
  constructor
  · intro h
    have hexp := hqt (a₁ := (mu i, i.rev.val + 1)) (a₂ := (mu j, j.rev.val)) (by
      simpa only [grid] using h)
    refine ⟨congrArg Prod.fst hexp, ?_⟩
    have hrev := congrArg Prod.snd hexp
    simp only [Fin.val_rev] at hrev
    lia
  · rintro ⟨hmu, hji⟩
    have hrev : i.rev.val + 1 = j.rev.val := by
      simp only [Fin.val_rev]
      lia
    simp only [grid, hmu, hrev]

/-- Legality is equivalent to the absence of a shifted lower row immediately below an
unshifted equal row. -/
theorem isLegal_iff_no_bad_pair (mu : Nat.PartitionVector N) (I : Finset (Fin N)) :
    IsLegal mu I ↔
      ∀ i ∈ I, ∀ j ∉ I, ¬(mu i = mu j ∧ j.val + 1 = i.val) := by
  constructor
  · intro hlegal i hi j hj hbad
    have hji : j ≤ i := by
      exact Fin.mk_le_mk.mpr (by lia)
    have h := hlegal hji
    simp only [increment, hi, hj, ite_true, ite_false, hbad.1] at h
    lia
  · intro hbad
    cases N with
    | zero => exact fun i ↦ Fin.elim0 i
    | succ n =>
        rw [IsLegal, Fin.antitone_iff_succ_le]
        intro i
        have hmu := mu.antitone (Fin.castSucc_le_succ i)
        by_cases hu : i.castSucc ∈ I
        · by_cases hl : i.succ ∈ I
          · simpa [increment, hu, hl] using hmu
          · simp only [increment, hu, hl, ite_true, ite_false]
            exact hmu.trans (Nat.le_add_right _ _)
        · by_cases hl : i.succ ∈ I
          · have hne : mu i.succ ≠ mu i.castSucc := by
              intro heq
              exact hbad i.succ hl i.castSucc hu
                ⟨heq, by simp⟩
            simp only [increment, hu, hl, ite_false, ite_true]
            lia
          · simpa [increment, hu, hl] using hmu

/-- The rational factor associated to an ordered pair of shifted and unshifted rows. -/
def gridFactor [Field K] (q t : K) (mu : Nat.PartitionVector N)
    (i j : Fin N) : K :=
  numeratorFactor q t mu i j / (grid q t mu i - grid q t mu j)

/-- The coefficient `A_I` evaluated on the partition grid. -/
def gridCoefficient [Field K] (q t : K) (mu : Nat.PartitionVector N)
    (I : Finset (Fin N)) : K :=
  t ^ (I.card * (I.card - 1) / 2) *
    ∏ i ∈ I, ∏ j ∈ Finset.univ \ I, gridFactor q t mu i j

/-- The grid coefficient, in the notation used for the Pieri recurrence. -/
abbrev B [Field K] (q t : K) (mu : Nat.PartitionVector N)
    (I : Finset (Fin N)) : K :=
  gridCoefficient q t mu I

/-- The specialized coefficient is nonzero exactly when the incremented rows form a
partition. -/
theorem gridCoefficient_ne_zero_iff [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (mu : Nat.PartitionVector N)
    (I : Finset (Fin N)) :
    gridCoefficient q t mu I ≠ 0 ↔ IsLegal mu I := by
  rw [isLegal_iff_no_bad_pair]
  constructor
  · intro hcoeff i hi j hj hbad
    apply hcoeff
    rw [gridCoefficient]
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero hi
    apply Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩)
    rw [gridFactor]
    rw [(numeratorFactor_eq_zero_iff hqt mu i j).mpr hbad, zero_div]
  · intro hlegal
    rw [gridCoefficient]
    apply mul_ne_zero
    · exact pow_ne_zero _ hqt.ne_zero.2
    · rw [Finset.prod_ne_zero_iff]
      intro i hi
      rw [Finset.prod_ne_zero_iff]
      intro j hj
      rw [gridFactor]
      apply div_ne_zero
      · intro hzero
        exact hlegal i hi j (Finset.mem_sdiff.mp hj).2
          ((numeratorFactor_eq_zero_iff hqt mu i j).mp hzero)
      · apply grid_sub_ne_zero hqt mu
        intro hij
        subst j
        exact (Finset.mem_sdiff.mp hj).2 hi

/-- Simultaneously scale the variables whose indices belong to `I`. -/
def scaleSubset [CommSemiring K] (c : K) (I : Finset (Fin N)) :
    MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K :=
  MvPolynomial.aeval fun i ↦ if i ∈ I then c • MvPolynomial.X i else MvPolynomial.X i

/-- A simultaneous variable scaling acts on a variable according to membership in the subset. -/
@[simp]
theorem scaleSubset_X [CommSemiring K] (c : K) (I : Finset (Fin N)) (i : Fin N) :
    scaleSubset c I (MvPolynomial.X i) =
      if i ∈ I then c • MvPolynomial.X i else MvPolynomial.X i := by
  simp [scaleSubset]

/-- Evaluation after scaling a subset is evaluation at the correspondingly scaled point. -/
theorem eval_scaleSubset [CommSemiring K] (c : K) (I : Finset (Fin N))
    (x : Fin N → K) (f : MvPolynomial (Fin N) K) :
    MvPolynomial.eval x (scaleSubset c I f) =
      MvPolynomial.eval (fun i ↦ if i ∈ I then c * x i else x i) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [scaleSubset]
  | add f g hf hg => simp [hf, hg]
  | mul_X f i hf =>
      simp only [map_mul, scaleSubset_X, hf, MvPolynomial.eval_X]
      by_cases hi : i ∈ I <;> simp [hi]

/-- Scaling the variables in `I` by `q` moves the partition grid to the raw incremented grid. -/
theorem eval_scaleSubset_grid [Field K] (q t : K) (mu : Nat.PartitionVector N)
    (I : Finset (Fin N)) (f : MvPolynomial (Fin N) K) :
    MvPolynomial.eval (grid q t mu) (scaleSubset q I f) =
      MvPolynomial.eval
        (fun i ↦ q ^ increment mu I i * t ^ i.rev.val) f := by
  rw [eval_scaleSubset]
  apply congrArg (fun y : Fin N → K ↦ MvPolynomial.eval y f)
  funext i
  by_cases hi : i ∈ I
  · simp only [hi, ite_true, increment, pow_succ]
    rw [grid]
    ring
  · simp [hi, increment, grid]

/-- On a legal subset, scaling by `q` moves the grid to the grid of the incremented partition. -/
theorem eval_scaleSubset_grid_of_isLegal [Field K] (q t : K)
    (mu : Nat.PartitionVector N) (I : Finset (Fin N)) (hI : IsLegal mu I)
    (f : MvPolynomial (Fin N) K) :
    MvPolynomial.eval (grid q t mu) (scaleSubset q I f) =
      MvPolynomial.eval (grid q t (incrementPartition mu I hI)) f := by
  rw [eval_scaleSubset_grid]
  congr 1

/-- The Vandermonde does not vanish on a power-pair injective partition grid. -/
theorem eval_vandermonde_grid_ne_zero [Field K] {q t : K}
    (hqt : PowerPairInjective q t) (mu : Nat.PartitionVector N) :
    MvPolynomial.eval (grid q t mu) (MvPolynomial.vandermonde N K) ≠ 0 := by
  simp only [MvPolynomial.vandermonde, map_prod, map_sub, MvPolynomial.eval_X]
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  apply grid_sub_ne_zero hqt mu
  exact (Finset.mem_Ioi.mp hj).ne

/-- A summand in the grid recurrence, defined to be zero for an illegal row subset. -/
def gridRecurrenceTerm [Field K] (q t : K) (mu : Nat.PartitionVector N)
    (f : MvPolynomial (Fin N) K) (I : Finset (Fin N)) : K := by
  classical
  exact if hI : IsLegal mu I then
      B q t mu I * MvPolynomial.eval (grid q t (incrementPartition mu I hI)) f
    else 0

/-- A conditional grid recurrence.  The extra ratio hypothesis isolates the elementary
finite-product identity `T_(t,I)(a_delta)/a_delta = A_I`; no Macdonald-polynomial theorem is
used. -/
theorem gridRecurrence_of_vandermondeRatio [Field K] {q t c : K}
    (hqt : PowerPairInjective q t) (mu : Nat.PartitionVector N) (r : ℕ)
    (f g : MvPolynomial (Fin N) K)
    (hnum :
      MvPolynomial.vandermonde N K * g =
        ∑ I ∈ Finset.univ.powersetCard r,
          scaleSubset t I (MvPolynomial.vandermonde N K) * scaleSubset q I f)
    (heigen : g = c • f)
    (hratio : ∀ I ∈ Finset.univ.powersetCard r,
      MvPolynomial.eval (grid q t mu)
          (scaleSubset t I (MvPolynomial.vandermonde N K)) =
        MvPolynomial.eval (grid q t mu) (MvPolynomial.vandermonde N K) *
          B q t mu I) :
    c * MvPolynomial.eval (grid q t mu) f =
      ∑ I ∈ Finset.univ.powersetCard r, gridRecurrenceTerm q t mu f I := by
  let v := MvPolynomial.eval (grid q t mu) (MvPolynomial.vandermonde N K)
  have hv : v ≠ 0 := eval_vandermonde_grid_ne_zero hqt mu
  apply mul_left_cancel₀ hv
  have heval := congrArg (MvPolynomial.eval (grid q t mu)) hnum
  simp only [map_mul, map_sum] at heval
  have heval_smul :
      MvPolynomial.eval (grid q t mu) (c • f) =
        c * MvPolynomial.eval (grid q t mu) f := by
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul]
    simp
  calc
    v * (c * MvPolynomial.eval (grid q t mu) f) =
        MvPolynomial.eval (grid q t mu) (MvPolynomial.vandermonde N K) *
          MvPolynomial.eval (grid q t mu) g := by
      rw [heigen, heval_smul]
    _ = ∑ I ∈ Finset.univ.powersetCard r,
          MvPolynomial.eval (grid q t mu)
            (scaleSubset t I (MvPolynomial.vandermonde N K)) *
          MvPolynomial.eval (grid q t mu) (scaleSubset q I f) := heval
    _ = ∑ I ∈ Finset.univ.powersetCard r,
          v * (B q t mu I * MvPolynomial.eval
            (fun i ↦ q ^ increment mu I i * t ^ i.rev.val) f) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [hratio I hI, eval_scaleSubset_grid]
      simp only [v]
      ring
    _ = ∑ I ∈ Finset.univ.powersetCard r,
          v * gridRecurrenceTerm q t mu f I := by
      apply Finset.sum_congr rfl
      intro I hI
      by_cases hlegal : IsLegal mu I
      · simp only [gridRecurrenceTerm, hlegal, dite_true]
        have hmove :
            MvPolynomial.eval
                (fun i ↦ q ^ increment mu I i * t ^ i.rev.val) f =
              MvPolynomial.eval (grid q t (incrementPartition mu I hlegal)) f := by
          rw [← eval_scaleSubset_grid q t mu I f,
            eval_scaleSubset_grid_of_isLegal q t mu I hlegal f]
        rw [hmove]
      · simp only [gridRecurrenceTerm, hlegal, dite_false]
        have hzero : B q t mu I = 0 := by
          simpa only [not_not] using
            mt (gridCoefficient_ne_zero_iff hqt mu I).mp hlegal
        simp [hzero]
    _ = v * ∑ I ∈ Finset.univ.powersetCard r,
          gridRecurrenceTerm q t mu f I := by
      rw [Finset.mul_sum]

end Nat.PartitionVector.Macdonald
