/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.NNRat.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Nonnegative coefficients and traces of matrix products

This file defines coefficientwise nonnegativity for multivariate polynomials over an ordered
commutative semiring. It proves closure under the semiring operations and finite sums and
products, and shows that the trace of a finite product of square matrices with such entries
again has nonnegative coefficients (including the empty product).

## Main declarations

* `MvPolynomial.HasNonnegCoeffs`
* `Matrix.hasNonnegCoeffs_trace_list_prod`
-/

@[expose] public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] [PartialOrder R]

/-- A multivariate polynomial has nonnegative coefficients if each of its coefficients is
nonnegative. -/
def HasNonnegCoeffs (p : MvPolynomial σ R) : Prop :=
  ∀ d, 0 ≤ p.coeff d

namespace HasNonnegCoeffs

/-- The zero multivariate polynomial has nonnegative coefficients. -/
theorem zero : HasNonnegCoeffs (0 : MvPolynomial σ R) := by
  intro d
  simp

/-- The unit multivariate polynomial has nonnegative coefficients. -/
theorem one [IsOrderedRing R] : HasNonnegCoeffs (1 : MvPolynomial σ R) := by
  classical
  intro d
  rw [MvPolynomial.coeff_one]
  split_ifs
  · exact zero_le_one
  · exact le_rfl

/-- A nonnegative constant gives a multivariate polynomial with nonnegative coefficients. -/
theorem C {a : R} (ha : 0 ≤ a) : HasNonnegCoeffs (C a : MvPolynomial σ R) := by
  classical
  intro d
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact ha
  · exact le_rfl

/-- A variable, viewed as a multivariate polynomial, has nonnegative coefficients. -/
theorem X [IsOrderedRing R] (i : σ) : HasNonnegCoeffs (X i : MvPolynomial σ R) := by
  classical
  intro d
  rw [MvPolynomial.coeff_X]
  split_ifs
  · exact zero_le_one
  · exact le_rfl

variable [IsOrderedRing R]

/-- A sum of multivariate polynomials with nonnegative coefficients has nonnegative
coefficients. -/
theorem add {p q : MvPolynomial σ R} (hp : p.HasNonnegCoeffs) (hq : q.HasNonnegCoeffs) :
    (p + q).HasNonnegCoeffs := by
  intro d
  simpa using add_nonneg (hp d) (hq d)

/-- A product of multivariate polynomials with nonnegative coefficients has nonnegative
coefficients. -/
theorem mul {p q : MvPolynomial σ R} (hp : p.HasNonnegCoeffs) (hq : q.HasNonnegCoeffs) :
    (p * q).HasNonnegCoeffs := by
  classical
  intro d
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (hp x.1) (hq x.2)

/-- A finite sum of multivariate polynomials with nonnegative coefficients has nonnegative
coefficients. -/
theorem finset_sum {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial σ R}
    (hf : ∀ i ∈ s, (f i).HasNonnegCoeffs) : (∑ i ∈ s, f i).HasNonnegCoeffs := by
  classical
  intro d
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_nonneg fun i hi ↦ hf i hi d

/-- A finite product of multivariate polynomials with nonnegative coefficients has nonnegative
coefficients. -/
theorem finset_prod {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial σ R}
    (hf : ∀ i ∈ s, (f i).HasNonnegCoeffs) : (∏ i ∈ s, f i).HasNonnegCoeffs := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one : HasNonnegCoeffs (1 : MvPolynomial σ R))
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).mul
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- A list sum of multivariate polynomials with nonnegative coefficients has nonnegative
coefficients. -/
theorem list_sum {l : List (MvPolynomial σ R)} (hl : ∀ p ∈ l, p.HasNonnegCoeffs) :
    l.sum.HasNonnegCoeffs := by
  induction l with
  | nil => simpa using (zero : HasNonnegCoeffs (0 : MvPolynomial σ R))
  | cons p l ih =>
      rw [List.sum_cons]
      exact (hl p (by simp)).add (ih fun q hq ↦ hl q (by simp [hq]))

/-- A list product of multivariate polynomials with nonnegative coefficients has nonnegative
coefficients. -/
theorem list_prod {l : List (MvPolynomial σ R)} (hl : ∀ p ∈ l, p.HasNonnegCoeffs) :
    l.prod.HasNonnegCoeffs := by
  induction l with
  | nil => simpa using (one : HasNonnegCoeffs (1 : MvPolynomial σ R))
  | cons p l ih =>
      rw [List.prod_cons]
      exact (hl p (by simp)).mul (ih fun q hq ↦ hl q (by simp [hq]))

/-- Mapping a multivariate polynomial with nonnegative rational coefficients to rational
coefficients produces a polynomial with nonnegative coefficients. -/
theorem map_nnrat (p : MvPolynomial σ ℚ≥0) :
    HasNonnegCoeffs (MvPolynomial.map NNRat.coeHom p) := by
  intro d
  rw [MvPolynomial.coeff_map]
  exact NNRat.coe_nonneg _

end HasNonnegCoeffs

end MvPolynomial

namespace Matrix

variable {m n : Type*}

variable {σ R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]

/-- The identity matrix has entries with nonnegative polynomial coefficients. -/
theorem hasNonnegCoeffs_one [DecidableEq n] :
    ∀ i j, MvPolynomial.HasNonnegCoeffs ((1 : Matrix n n (MvPolynomial σ R)) i j) := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa using
      (MvPolynomial.HasNonnegCoeffs.one :
        MvPolynomial.HasNonnegCoeffs (1 : MvPolynomial σ R))
  · simpa [Matrix.one_apply, hij] using
      (MvPolynomial.HasNonnegCoeffs.zero :
        MvPolynomial.HasNonnegCoeffs (0 : MvPolynomial σ R))

/-- A product of matrices whose entries have nonnegative polynomial coefficients again has
entries with nonnegative coefficients. -/
theorem hasNonnegCoeffs_mul {o : Type*} [Fintype m]
    {A : Matrix n m (MvPolynomial σ R)} {B : Matrix m o (MvPolynomial σ R)}
    (hA : ∀ i j, MvPolynomial.HasNonnegCoeffs (A i j))
    (hB : ∀ i j, MvPolynomial.HasNonnegCoeffs (B i j)) :
    ∀ i j, MvPolynomial.HasNonnegCoeffs ((A * B) i j) := by
  classical
  intro i j
  rw [Matrix.mul_apply]
  apply MvPolynomial.HasNonnegCoeffs.finset_sum
  intro k _
  exact (hA i k).mul (hB k j)

/-- A finite product of square matrices whose entries have nonnegative polynomial coefficients
has entries with nonnegative coefficients, including for the empty product. -/
theorem hasNonnegCoeffs_list_prod [Fintype n] [DecidableEq n]
    {l : List (Matrix n n (MvPolynomial σ R))}
    (hl : ∀ A ∈ l, ∀ i j, MvPolynomial.HasNonnegCoeffs (A i j)) :
    ∀ i j, MvPolynomial.HasNonnegCoeffs (l.prod i j) := by
  induction l with
  | nil => simpa using (hasNonnegCoeffs_one (σ := σ) (R := R) (n := n))
  | cons A l ih =>
      rw [List.prod_cons]
      exact hasNonnegCoeffs_mul
        (hl A (by simp)) (ih fun B hB ↦ hl B (by simp [hB]))

/-- The trace of a matrix with coefficientwise nonnegative diagonal entries has nonnegative
coefficients. -/
theorem hasNonnegCoeffs_trace [Fintype n] {A : Matrix n n (MvPolynomial σ R)}
    (hA : ∀ i, MvPolynomial.HasNonnegCoeffs (A i i)) :
    MvPolynomial.HasNonnegCoeffs (trace A) := by
  classical
  rw [Matrix.trace]
  apply MvPolynomial.HasNonnegCoeffs.finset_sum
  intro i _
  exact hA i

/-- The trace of a finite product of matrices with coefficientwise nonnegative entries has
nonnegative coefficients, including for the empty product. -/
theorem hasNonnegCoeffs_trace_list_prod [Fintype n] [DecidableEq n]
    {l : List (Matrix n n (MvPolynomial σ R))}
    (hl : ∀ A ∈ l, ∀ i j, MvPolynomial.HasNonnegCoeffs (A i j)) :
    MvPolynomial.HasNonnegCoeffs (trace l.prod) := by
  apply hasNonnegCoeffs_trace
  intro i
  exact hasNonnegCoeffs_list_prod hl i i

end Matrix
