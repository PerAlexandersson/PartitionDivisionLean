/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Regular values of polynomial quotients

This file packages a polynomial quotient that is regular at a specified point.  The package is
designed to compose under multiplication and includes the cancellation of `1 - X` in quotients
of polynomials of the form `1 - X ^ n`.
-/

@[expose] public section

open Finset

namespace Polynomial

variable {F : Type*} [Field F]

noncomputable section

/-- Evidence that `num / den` has a presentation `reducedNum / reducedDen` whose denominator
does not vanish at `x`.  The cross-multiplication identity avoids choosing a fraction-field
normal form. -/
structure IsRegularQuotientAt (num den : F[X]) (x : F) where
  /-- The numerator after cancellation. -/
  reducedNum : F[X]
  /-- The denominator after cancellation. -/
  reducedDen : F[X]
  /-- The original and reduced presentations define the same rational function. -/
  cross_mul : num * reducedDen = den * reducedNum
  /-- The reduced denominator does not vanish at the evaluation point. -/
  eval_reducedDen_ne_zero : reducedDen.eval x ≠ 0

namespace IsRegularQuotientAt

/-- The regular value of a polynomial quotient. -/
def value {num den : F[X]} {x : F} (h : IsRegularQuotientAt num den x) : F :=
  h.reducedNum.eval x / h.reducedDen.eval x

/-- A quotient whose original denominator is nonzero is regular without cancellation. -/
def ofDenominatorNe {num den : F[X]} {x : F} (hden : den.eval x ≠ 0) :
    IsRegularQuotientAt num den x where
  reducedNum := num
  reducedDen := den
  cross_mul := mul_comm _ _
  eval_reducedDen_ne_zero := hden

/-- Regular polynomial quotients are closed under multiplication. -/
def mul {num₁ den₁ num₂ den₂ : F[X]} {x : F}
    (h₁ : IsRegularQuotientAt num₁ den₁ x)
    (h₂ : IsRegularQuotientAt num₂ den₂ x) :
    IsRegularQuotientAt (num₁ * num₂) (den₁ * den₂) x where
  reducedNum := h₁.reducedNum * h₂.reducedNum
  reducedDen := h₁.reducedDen * h₂.reducedDen
  cross_mul := by
    rw [mul_mul_mul_comm, h₁.cross_mul, h₂.cross_mul, mul_mul_mul_comm]
  eval_reducedDen_ne_zero := by
    rw [eval_mul]
    exact mul_ne_zero h₁.eval_reducedDen_ne_zero h₂.eval_reducedDen_ne_zero

/-- The value of a product of regular polynomial quotients is the product of their values. -/
theorem value_mul {num₁ den₁ num₂ den₂ : F[X]} {x : F}
    (h₁ : IsRegularQuotientAt num₁ den₁ x)
    (h₂ : IsRegularQuotientAt num₂ den₂ x) :
    (h₁.mul h₂).value = h₁.value * h₂.value := by
  simp only [value, mul, eval_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

end IsRegularQuotientAt

/-- The geometric-sum polynomial `1 + X + ... + X^(n-1)`. -/
def geometricSum (n : ℕ) : F[X] := ∑ i ∈ range n, X ^ i

/-- Evaluation of the geometric-sum polynomial at one gives the natural number `n`. -/
@[simp]
theorem eval_one_geometricSum (n : ℕ) : (geometricSum n : F[X]).eval 1 = n := by
  simp [geometricSum]

/-- Cancelling `1 - X` makes `(1 - X^n) / (1 - X^m)` regular at one when both exponents are
positive. -/
def isRegularQuotientAt_one_sub_X_pow [CharZero F] (n m : ℕ) (hm : 0 < m) :
    IsRegularQuotientAt (1 - X ^ n) (1 - X ^ m) (1 : F) where
  reducedNum := geometricSum n
  reducedDen := geometricSum m
  cross_mul := by
    rw [mul_comm (1 - X ^ n), mul_comm (1 - X ^ m)]
    rw [show (1 - X ^ n) = geometricSum n * (1 - X) by
      simpa [geometricSum] using (geom_sum_mul_neg (X : F[X]) n).symm]
    rw [show (1 - X ^ m) = geometricSum m * (1 - X) by
      simpa [geometricSum] using (geom_sum_mul_neg (X : F[X]) m).symm]
    ac_rfl
  eval_reducedDen_ne_zero := by
    rw [eval_one_geometricSum]
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)

/-- The regular value at one of `(1 - X^n) / (1 - X^m)` is `n / m`. -/
theorem value_isRegularQuotientAt_one_sub_X_pow [CharZero F] (n m : ℕ) (hm : 0 < m) :
    (isRegularQuotientAt_one_sub_X_pow n m hm :
      IsRegularQuotientAt (1 - X ^ n) (1 - X ^ m) (1 : F)).value = n / m := by
  simp [IsRegularQuotientAt.value, isRegularQuotientAt_one_sub_X_pow]

/-- The polynomial `1 - C(z) X^n`. -/
def oneSubCMulXPow (z : F) (n : ℕ) : F[X] := 1 - C z * X ^ n

/-- A quotient `(1 - C(z) X^n) / (1 - C(z) X^m)` has a presentation regular at one.  Its
regular value is `n / m` when `z = 1`, and is one otherwise. -/
theorem exists_regularPresentation_oneSubCMulXPow [CharZero F]
    (z : F) (n m : ℕ) (hm : 0 < m) :
    ∃ p r : F[X], oneSubCMulXPow z n * r = oneSubCMulXPow z m * p ∧
      r.eval 1 ≠ 0 ∧
      (z = 1 → p.eval 1 / r.eval 1 = (n : F) / m) ∧
      (z ≠ 1 → p.eval 1 / r.eval 1 = 1) := by
  by_cases hz : z = 1
  · subst z
    refine ⟨geometricSum n, geometricSum m, ?_, ?_, ?_, ?_⟩
    · rw [show oneSubCMulXPow (1 : F) n = geometricSum n * (1 - X) by
        simpa [oneSubCMulXPow, geometricSum] using
          (geom_sum_mul_neg (X : F[X]) n).symm]
      rw [show oneSubCMulXPow (1 : F) m = geometricSum m * (1 - X) by
        simpa [oneSubCMulXPow, geometricSum] using
          (geom_sum_mul_neg (X : F[X]) m).symm]
      ac_rfl
    · rw [eval_one_geometricSum]
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
    · intro
      exact value_isRegularQuotientAt_one_sub_X_pow n m hm
    · simp
  · refine ⟨oneSubCMulXPow z n, oneSubCMulXPow z m, mul_comm _ _, ?_, ?_, ?_⟩
    · simpa [oneSubCMulXPow] using sub_ne_zero.mpr (Ne.symm hz)
    · simp [hz]
    · intro
      simp [oneSubCMulXPow, sub_ne_zero.mpr (Ne.symm hz)]

end

end Polynomial
