/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Coordinatewise exponent filters for multivariate polynomials

This file defines `MvPolynomial.exponentFilter k`, the linear projection onto the monomials whose
exponents are all divisible by `k`, and `MvPolynomial.exponentDiv k`, which divides those
exponents by `k`, so that `exponentFilter k f = expand k (exponentDiv k f)`. Both commute with
permutations of the variables and so preserve symmetry.
It also proves that averaging all coordinatewise twists by a primitive root of unity is a scalar
multiple of the exponent filter.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Raising every variable to a common power preserves symmetry. -/
theorem IsSymmetric.expand {f : MvPolynomial σ R} (hf : f.IsSymmetric) (k : ℕ) :
    (expand k f).IsSymmetric := by
  intro e
  rw [rename_expand, hf e]

/-- A multidegree is coordinatewise divisible by `k` if each of its exponents is divisible by
`k`. -/
def ExponentsDivisibleBy (k : ℕ) (d : σ →₀ ℕ) : Prop :=
  ∀ i, k ∣ d i

/-- Divide every exponent of a multidegree by `k`. -/
def exponentQuotient (k : ℕ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.mapRange (· / k) (Nat.zero_div k)

/-- Evaluation of `exponentQuotient` divides each coordinate by `k`. -/
@[simp]
theorem exponentQuotient_apply (k : ℕ) (d : σ →₀ ℕ) (i : σ) :
    exponentQuotient k d i = d i / k :=
  rfl

private theorem smul_exponentQuotient {k : ℕ} {d : σ →₀ ℕ}
    (hd : ExponentsDivisibleBy k d) : k • exponentQuotient k d = d := by
  ext i
  simp [exponentQuotient, Nat.mul_div_cancel' (hd i)]

private theorem exponentsDivisibleBy_mapDomain_equiv (k : ℕ) (e : σ ≃ τ) (d : σ →₀ ℕ) :
    ExponentsDivisibleBy k (d.mapDomain e) ↔ ExponentsDivisibleBy k d := by
  constructor
  · intro h i
    simpa using h (e i)
  · intro h i
    simpa using h (e.symm i)

private theorem exponentQuotient_mapDomain_equiv (k : ℕ) (e : σ ≃ τ) (d : σ →₀ ℕ) :
    exponentQuotient k (d.mapDomain e) = (exponentQuotient k d).mapDomain e := by
  ext i
  simp [exponentQuotient]

/-- The linear projection retaining precisely the monomials whose exponents are all divisible by
`k`. -/
def exponentFilter (k : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R where
  toFun f := by
    classical
    exact AddMonoidAlgebra.ofCoeff (f.coeff.filter (ExponentsDivisibleBy k))
  map_add' f g := by
    classical
    ext d
    simp [Finsupp.filter_apply]
  map_smul' r f := by
    classical
    ext d
    simp [Finsupp.filter_apply]

/-- The exponent filter keeps a coefficient exactly when its multidegree is coordinatewise
divisible by `k`. -/
@[simp]
theorem coeff_exponentFilter (k : ℕ) (f : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (exponentFilter k f).coeff d = if ExponentsDivisibleBy k d then f.coeff d else 0 :=
  by
    classical
    rfl

/-- The exponent filter either keeps or discards a monomial according to its multidegree. -/
@[simp]
theorem exponentFilter_monomial (k : ℕ) (d : σ →₀ ℕ) (r : R) :
    exponentFilter k (monomial d r) =
      if ExponentsDivisibleBy k d then monomial d r else 0 := by
  classical
  by_cases hd : ExponentsDivisibleBy k d
  · rw [ite_eq_left hd]
    ext e
    by_cases he : d = e
    · subst e
      simp [hd]
    · simp [coeff_monomial, he]
  · rw [ite_eq_right hd]
    ext e
    by_cases he : d = e
    · subst e
      simp [hd]
    · simp [coeff_monomial, he]

/-- Divide the exponents of the monomials retained by `exponentFilter`. -/
def exponentDiv (k : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  by
    classical
    exact (Finsupp.lsum R fun d ↦
      if ExponentsDivisibleBy k d then monomial (exponentQuotient k d) else 0) ∘ₗ
        (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

/-- Exponent division divides the multidegree of a divisible monomial and kills any other
monomial. -/
@[simp]
theorem exponentDiv_monomial (k : ℕ) (d : σ →₀ ℕ) (r : R) :
    exponentDiv k (monomial d r) =
      if ExponentsDivisibleBy k d then monomial (exponentQuotient k d) r else 0 := by
  classical
  by_cases hd : ExponentsDivisibleBy k d <;> simp [exponentDiv, hd]

/-- Filtering is expansion after division of all retained exponents. -/
theorem exponentFilter_eq_expand_exponentDiv (k : ℕ) (f : MvPolynomial σ R) :
    exponentFilter k f = expand k (exponentDiv k f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
      by_cases hd : ExponentsDivisibleBy k d
      · simp [hd, smul_exponentQuotient hd]
      · simp [hd]
  | add f g hf hg => simp [hf, hg]

/-- The exponent filter commutes with equivalences of the variable types. -/
theorem rename_exponentFilter (k : ℕ) (e : σ ≃ τ) (f : MvPolynomial σ R) :
    rename e (exponentFilter k f) = exponentFilter k (rename e f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
      rw [exponentFilter_monomial, rename_monomial, exponentFilter_monomial]
      rw [exponentsDivisibleBy_mapDomain_equiv]
      by_cases hd : ExponentsDivisibleBy k d <;> simp [hd, rename_monomial]
  | add f g hf hg => simp [hf, hg]

/-- Division of retained exponents commutes with equivalences of the variable types. -/
theorem rename_exponentDiv (k : ℕ) (e : σ ≃ τ) (f : MvPolynomial σ R) :
    rename e (exponentDiv k f) = exponentDiv k (rename e f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
      rw [exponentDiv_monomial, rename_monomial, exponentDiv_monomial]
      rw [exponentsDivisibleBy_mapDomain_equiv]
      by_cases hd : ExponentsDivisibleBy k d
      · simp [hd, rename_monomial, exponentQuotient_mapDomain_equiv]
      · simp [hd]
  | add f g hf hg => simp [hf, hg]

/-- The coordinatewise exponent filter preserves symmetry. -/
theorem IsSymmetric.exponentFilter {f : MvPolynomial σ R} (hf : f.IsSymmetric) (k : ℕ) :
    (exponentFilter k f).IsSymmetric := by
  intro e
  rw [rename_exponentFilter, hf e]

/-- Coordinatewise division of retained exponents preserves symmetry. -/
theorem IsSymmetric.exponentDiv {f : MvPolynomial σ R} (hf : f.IsSymmetric) (k : ℕ) :
    (exponentDiv k f).IsSymmetric := by
  intro e
  rw [rename_exponentDiv, hf e]

end MvPolynomial

namespace IsPrimitiveRoot

variable {K : Type*} [CommRing K] [IsDomain K] {ζ : K} {k : ℕ}

/-- The sum of the `m`th powers of all powers of a primitive `k`th root is `k` when
`k ∣ m`, and is zero otherwise. -/
theorem sum_pow_mul_eq_ite_dvd (hζ : IsPrimitiveRoot ζ k) (m : ℕ) :
    ∑ j : Fin k, ζ ^ (j.val * m) = if k ∣ m then (k : K) else 0 := by
  have hsum : (∑ j : Fin k, ζ ^ (j.val * m)) = ∑ j : Fin k, (ζ ^ m) ^ j.val := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← pow_mul, Nat.mul_comm]
  rw [hsum, Fin.sum_univ_eq_sum_range]
  by_cases hm : k ∣ m
  · rw [ite_eq_left hm]
    have hz : ζ ^ m = 1 := (hζ.pow_eq_one_iff_dvd m).2 hm
    simp [hz]
  · rw [ite_eq_right hm]
    have hz : ζ ^ m ≠ 1 := fun h ↦ hm ((hζ.pow_eq_one_iff_dvd m).1 h)
    have hprod : (ζ ^ m - 1) * ∑ j ∈ Finset.range k, (ζ ^ m) ^ j = 0 := by
      rw [mul_geom_sum, ← pow_mul, mul_comm m k, pow_mul, hζ.pow_eq_one, one_pow,
        sub_self]
    rw [mul_eq_zero] at hprod
    exact hprod.resolve_left (sub_ne_zero.mpr hz)

end IsPrimitiveRoot

namespace MvPolynomial

variable {K : Type*} [CommSemiring K]

/-- Twist each variable `X i` by the power `ζ ^ (j i).val`. -/
def rootTwist {σ : Type*} {k : ℕ} (ζ : K) (j : σ → Fin k) :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval fun i ↦ C (ζ ^ (j i).val) * X i

/-- A root twist multiplies a monomial by the corresponding character value. -/
theorem rootTwist_monomial {σ : Type*} [Fintype σ] {k : ℕ} (ζ : K) (j : σ → Fin k)
    (d : σ →₀ ℕ) (r : K) :
    rootTwist ζ j (monomial d r) =
      monomial d (r * ∏ i, ζ ^ ((j i).val * d i)) := by
  rw [rootTwist, aeval_monomial, Finsupp.prod_pow, monomial_eq]
  change C r * ∏ a, (C (ζ ^ (j a).val) * X a) ^ d a = _
  simp only [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod, pow_mul]
  rw [Finsupp.prod_pow, ← mul_assoc, ← C_mul]

end MvPolynomial

namespace MvPolynomial

variable {K : Type*} [CommRing K] [IsDomain K]

/-- Averaging the root twists of a monomial retains it exactly when all exponents are divisible
by the order of the primitive root. -/
theorem sum_rootTwist_monomial {σ : Type*} [Fintype σ] [DecidableEq σ] {k : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ k) (d : σ →₀ ℕ) (r : K) :
    ∑ j : σ → Fin k, rootTwist ζ j (monomial d r) =
      (k ^ Fintype.card σ) • exponentFilter k (monomial d r) := by
  classical
  simp_rw [rootTwist_monomial]
  rw [← map_sum, exponentFilter_monomial]
  by_cases hd : ExponentsDivisibleBy k d
  · rw [ite_eq_left hd]
    rw [← Nat.cast_smul_eq_nsmul K, ← (monomial d).map_smul]
    apply congrArg (monomial d)
    rw [← Finset.mul_sum,
      ← Fintype.prod_sum (fun i (j : Fin k) ↦ ζ ^ (j.val * d i))]
    simp_rw [hζ.sum_pow_mul_eq_ite_dvd]
    have hfactor : ∀ i, (if k ∣ d i then (k : K) else 0) = k := fun i ↦
      ite_eq_left (hd i)
    simp_rw [hfactor]
    simp [Nat.cast_pow, mul_comm]
  · rw [ite_eq_right hd, smul_zero, ← (monomial d).map_zero]
    apply congrArg (monomial d)
    rw [← Finset.mul_sum,
      ← Fintype.prod_sum (fun i (j : Fin k) ↦ ζ ^ (j.val * d i))]
    simp_rw [hζ.sum_pow_mul_eq_ite_dvd]
    change r * ∏ i, (if k ∣ d i then (k : K) else 0) = 0
    suffices (∏ i, (if k ∣ d i then (k : K) else 0)) = 0 by rw [this, mul_zero]
    obtain ⟨i, hi⟩ := not_forall.mp hd
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- The sum of all coordinatewise root twists is the order-to-the-number-of-variables multiple
of the coordinatewise exponent filter. -/
theorem sum_rootTwist_eq_nsmul_exponentFilter {σ : Type*} [Fintype σ] [DecidableEq σ]
    {k : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ k) (f : MvPolynomial σ K) :
    ∑ j : σ → Fin k, rootTwist ζ j f =
      (k ^ Fintype.card σ) • exponentFilter k f := by
  induction f using MvPolynomial.induction_on' with
  | monomial d r => exact sum_rootTwist_monomial hζ d r
  | add f g hf hg => simp [hf, hg, Finset.sum_add_distrib]

end MvPolynomial
