/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Antisymmetric multivariate polynomials

This file defines antisymmetric multivariate polynomials and the Vandermonde polynomial.  It
proves that identifying two variables detects divisibility by their difference, and that the
Vandermonde divides every antisymmetric polynomial over a domain of characteristic different
from two.  The quotient is symmetric.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace MvPolynomial

variable {σ R : Type*}

/-- Identify the variable `i` with the variable `j` in a multivariate polynomial. -/
def diagonalEval [DecidableEq σ] [CommSemiring R] (i j : σ) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun k ↦ X (Function.update id i j k)

private theorem X_sub_X_dvd_sub_diagonalEval [DecidableEq σ] [CommRing R]
    (i j : σ) (p : MvPolynomial σ R) :
    X i - X j ∣ p - diagonalEval i j p := by
  by_cases hij : i = j
  · subst j
    have hu : Function.update id i i = id := by
      funext k
      by_cases hk : k = i
      · subst k
        simp
      · simp [hk]
    simp [diagonalEval, hu]
  induction p using MvPolynomial.induction_on with
  | C a => simp [diagonalEval]
  | add p q hp hq =>
      simpa only [map_add, add_sub_add_comm] using hp.add hq
  | mul_X p k hp =>
      rcases hp with ⟨q, hq⟩
      by_cases hk : k = i
      · subst k
        refine ⟨q * X i + diagonalEval i j p, ?_⟩
        calc
          p * X i - diagonalEval i j (p * X i) =
              (p - diagonalEval i j p) * X i +
                diagonalEval i j p * (X i - X j) := by
            simp [diagonalEval, Function.update_apply]
            ring
          _ = (X i - X j) * q * X i +
                diagonalEval i j p * (X i - X j) := by rw [hq]
          _ = (X i - X j) * (q * X i + diagonalEval i j p) := by ring
      · refine ⟨q * X k, ?_⟩
        calc
          p * X k - diagonalEval i j (p * X k) =
              (p - diagonalEval i j p) * X k := by
            simp [diagonalEval, Function.update_apply, hk]
            ring
          _ = (X i - X j) * q * X k := by rw [hq]
          _ = (X i - X j) * (q * X k) := by ring

/-- A difference `X i - X j` divides a polynomial exactly when identifying `X i` with `X j`
makes the polynomial vanish. -/
theorem X_sub_X_dvd_iff_diagonalEval_eq_zero [DecidableEq σ] [CommRing R]
    (i j : σ) (p : MvPolynomial σ R) :
    X i - X j ∣ p ↔ diagonalEval i j p = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    simp [diagonalEval, Function.update_apply]
  · intro hp
    simpa [hp] using X_sub_X_dvd_sub_diagonalEval i j p

/-- A multivariate polynomial is antisymmetric if renaming its variables by a permutation
multiplies it by the sign of the permutation. -/
def IsAntisymmetric [Fintype σ] [DecidableEq σ] [CommRing R]
    (p : MvPolynomial σ R) : Prop :=
  ∀ e : Equiv.Perm σ, rename e p = (e.sign : ℤ) • p

namespace IsAntisymmetric

variable [Fintype σ] [DecidableEq σ] [CommRing R] {p q : MvPolynomial σ R}

/-- The zero polynomial is antisymmetric. -/
@[simp]
theorem zero : IsAntisymmetric (0 : MvPolynomial σ R) := by
  intro e
  simp

/-- A sum of antisymmetric polynomials is antisymmetric. -/
theorem add (hp : p.IsAntisymmetric) (hq : q.IsAntisymmetric) : (p + q).IsAntisymmetric := by
  intro e
  simp [hp e, hq e]

/-- A scalar multiple of an antisymmetric polynomial is antisymmetric. -/
theorem smul (r : R) (hp : p.IsAntisymmetric) : (r • p).IsAntisymmetric := by
  intro e
  simp [hp e, smul_comm]

/-- The product of an antisymmetric polynomial and a symmetric polynomial is antisymmetric. -/
theorem mul_isSymmetric (hp : p.IsAntisymmetric) (hq : q.IsSymmetric) :
    (p * q).IsAntisymmetric := by
  intro e
  rw [map_mul, hp e, hq e, smul_mul_assoc]

end IsAntisymmetric

/-- The Vandermonde polynomial, with factors oriented as `X i - X j` for `i < j`. -/
def vandermonde (n : ℕ) (R : Type*) [CommRing R] : MvPolynomial (Fin n) R :=
  ∏ i, ∏ j ∈ Finset.Ioi i, (X i - X j)

/-- The Vandermonde polynomial is antisymmetric. -/
theorem isAntisymmetric_vandermonde (n : ℕ) (R : Type*) [CommRing R] :
    IsAntisymmetric (vandermonde n R) := by
  intro e
  simp only [vandermonde, map_prod, map_sub, rename_X]
  have h := e.prod_Ioi_comp_eq_sign_mul_prod
    (R := MvPolynomial (Fin n) R) (f := fun i j ↦ X i - X j) (by simp)
  simpa using h

/-- The Vandermonde polynomial over a domain is nonzero. -/
theorem vandermonde_ne_zero (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] :
    vandermonde n R ≠ 0 := by
  rw [vandermonde, Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  exact sub_ne_zero.mpr (X_injective.ne (Finset.mem_Ioi.mp hj).ne)

private theorem update_id_ne_of_lt_of_lt {n : ℕ} {i j a b : Fin n}
    (hij : i < j) (hab : a < b) (hpair : (a, b) ≠ (i, j)) :
    Function.update id i j a ≠ Function.update id i j b := by
  intro h
  simp only [Function.update_apply] at h
  split at h <;> split at h <;> grind

private theorem diagonalEval_X_sub_X_ne_zero [CommRing R] [IsDomain R]
    {n : ℕ} {i j a b : Fin n} (hij : i < j) (hab : a < b)
    (hpair : (a, b) ≠ (i, j)) :
    diagonalEval i j (X a - X b : MvPolynomial (Fin n) R) ≠ 0 := by
  rw [map_sub]
  simp only [diagonalEval, aeval_X]
  exact sub_ne_zero.mpr (X_injective.ne (update_id_ne_of_lt_of_lt hij hab hpair))

private theorem diagonalEval_rename_swap [DecidableEq σ] [CommRing R]
    (i j : σ) (p : MvPolynomial σ R) :
    diagonalEval i j (rename (Equiv.swap i j) p) = diagonalEval i j p := by
  rw [diagonalEval, aeval_rename]
  apply AlgHom.congr_fun
  apply MvPolynomial.algHom_ext
  intro k
  simp only [aeval_X, Function.comp_apply]
  congr 1
  by_cases hki : k = i
  · subst k
    simp [Function.update_apply]
  by_cases hkj : k = j
  · subst k
    simp [Function.update_apply]
  · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

private theorem diagonalEval_eq_zero_of_isAntisymmetric [Fintype σ] [DecidableEq σ]
    [CommRing R] [IsDomain R] [CharZero R] {i j : σ} (hij : i ≠ j)
    {p : MvPolynomial σ R} (hp : p.IsAntisymmetric) : diagonalEval i j p = 0 := by
  have hswap : rename (Equiv.swap i j) p = -p := by
    simpa [Equiv.Perm.sign_swap hij] using hp (Equiv.swap i j)
  have hneg : diagonalEval i j p = -diagonalEval i j p := by
    calc
      diagonalEval i j p = diagonalEval i j (rename (Equiv.swap i j) p) :=
        (diagonalEval_rename_swap i j p).symm
      _ = diagonalEval i j (-p) := congrArg (diagonalEval i j) hswap
      _ = -diagonalEval i j p := map_neg (diagonalEval i j) p
  have hmul : (2 : MvPolynomial σ R) * diagonalEval i j p = 0 := by
    simpa only [two_mul] using (eq_neg_iff_add_eq_zero.mp hneg)
  exact (mul_eq_zero.mp hmul).resolve_left (by exact_mod_cast (two_ne_zero : (2 : R) ≠ 0))

private theorem prod_X_sub_X_dvd_of_diagonalEval_eq_zero [CommRing R] [IsDomain R]
    {n : ℕ} {s : Finset (Σ _ : Fin n, Fin n)} {p : MvPolynomial (Fin n) R}
    (hs : ∀ a ∈ s, a.1 < a.2)
    (hp : ∀ a ∈ s, diagonalEval a.1 a.2 p = 0) :
    (∏ a ∈ s, (X a.1 - X a.2 : MvPolynomial (Fin n) R)) ∣ p := by
  induction s using Finset.induction_on generalizing p with
  | empty => simp
  | @insert a s ha ih =>
      have ha_lt : a.1 < a.2 := hs a (Finset.mem_insert_self a s)
      have ha_dvd : (X a.1 - X a.2 : MvPolynomial (Fin n) R) ∣ p :=
        (X_sub_X_dvd_iff_diagonalEval_eq_zero a.1 a.2 p).mpr
          (hp a (Finset.mem_insert_self a s))
      rcases ha_dvd with ⟨q, hq⟩
      have hq_zero : ∀ b ∈ s, diagonalEval b.1 b.2 q = 0 := by
        intro b hb
        have hb_lt : b.1 < b.2 := hs b (Finset.mem_insert_of_mem hb)
        have hp_zero := hp b (Finset.mem_insert_of_mem hb)
        have hmapped := congrArg (diagonalEval b.1 b.2) hq
        rw [map_mul, hp_zero] at hmapped
        exact (mul_eq_zero.mp hmapped.symm).resolve_left
          (diagonalEval_X_sub_X_ne_zero hb_lt ha_lt fun hba ↦ by
            have hab : a = b := by
              apply Sigma.ext
              · exact congrArg Prod.fst hba
              · exact heq_of_eq (congrArg Prod.snd hba)
            subst b
            exact ha hb)
      rcases ih (fun b hb ↦ hs b (Finset.mem_insert_of_mem hb)) hq_zero with ⟨r, hr⟩
      refine ⟨r, ?_⟩
      rw [Finset.prod_insert ha, hq, hr, mul_assoc]

/-- Over a domain of characteristic zero, every antisymmetric polynomial is divisible by the
Vandermonde polynomial. -/
theorem vandermonde_dvd_of_isAntisymmetric [CommRing R] [IsDomain R] [CharZero R]
    {n : ℕ} {p : MvPolynomial (Fin n) R} (hp : p.IsAntisymmetric) :
    vandermonde n R ∣ p := by
  rw [vandermonde, Finset.prod_sigma']
  refine prod_X_sub_X_dvd_of_diagonalEval_eq_zero
    (R := R) (n := n)
    (s := (Finset.univ : Finset (Fin n)).sigma fun i ↦ Finset.Ioi i) (p := p) ?_ ?_
  · intro a ha
    exact Finset.mem_Ioi.mp (Finset.mem_sigma.mp ha).2
  · intro a ha
    exact diagonalEval_eq_zero_of_isAntisymmetric (Finset.mem_Ioi.mp (Finset.mem_sigma.mp ha).2).ne
      hp

/-- If the product of the Vandermonde with a polynomial is antisymmetric, then the polynomial is
symmetric. -/
theorem isSymmetric_of_vandermonde_mul_isAntisymmetric [CommRing R] [IsDomain R]
    {n : ℕ} {q : MvPolynomial (Fin n) R}
    (h : (vandermonde n R * q).IsAntisymmetric) : q.IsSymmetric := by
  intro e
  have he := h e
  rw [map_mul, isAntisymmetric_vandermonde n R e] at he
  rcases Int.units_eq_one_or e.sign with hs | hs
  · simp [hs] at he
    exact he.resolve_right (vandermonde_ne_zero n R)
  · simp [hs] at he
    exact he.resolve_right (vandermonde_ne_zero n R)

/-- An antisymmetric polynomial over a characteristic-zero domain is the Vandermonde times a
symmetric polynomial. -/
theorem exists_isSymmetric_mul_eq_of_isAntisymmetric [CommRing R] [IsDomain R] [CharZero R]
    {n : ℕ} {p : MvPolynomial (Fin n) R} (hp : p.IsAntisymmetric) :
    ∃ q : MvPolynomial (Fin n) R, q.IsSymmetric ∧ p = vandermonde n R * q := by
  rcases vandermonde_dvd_of_isAntisymmetric hp with ⟨q, hq⟩
  refine ⟨q, ?_, hq⟩
  apply isSymmetric_of_vandermonde_mul_isAntisymmetric
  rwa [← hq]

end MvPolynomial
