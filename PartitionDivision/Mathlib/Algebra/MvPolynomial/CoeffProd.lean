/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Coefficients of finite products of multivariate polynomials

Mathlib proves `MvPowerSeries.coeff_prod`: a coefficient of a finite product of multivariate power
series is a sum, over the ways of splitting the exponent among the factors, of products of
coefficients.  This file transfers it to `MvPolynomial` through the coercion
`MvPolynomial σ R → MvPowerSeries σ R`, which lives in `Mathlib/RingTheory/MvPowerSeries/Basic.lean`
together with the other `MvPolynomial` coercion lemmas.

## Main results

* `MvPolynomial.coeff_prod`: the coefficient of `∏ i ∈ s, f i` at `d` is
  `∑ l ∈ s.finsuppAntidiag d, ∏ i ∈ s, (f i).coeff (l i)`.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {σ ι R : Type*} [CommSemiring R]

/-- **The coefficient of a finite product of multivariate polynomials**: the coefficient of
`∏ i ∈ s, f i` at `d` is the sum, over the decompositions `d = ∑ i ∈ s, l i`, of the products of
the coefficients of the factors `f i` at `l i`.  This is `MvPowerSeries.coeff_prod` read through
the coercion to power series. -/
theorem coeff_prod [DecidableEq σ] [DecidableEq ι] (s : Finset ι) (f : ι → MvPolynomial σ R)
    (d : σ →₀ ℕ) :
    (∏ i ∈ s, f i).coeff d = ∑ l ∈ s.finsuppAntidiag d, ∏ i ∈ s, (f i).coeff (l i) := by
  simp_rw [← coeff_coe (R := R), ← coeToMvPowerSeries.ringHom_apply, map_prod]
  exact MvPowerSeries.coeff_prod _ _ _

end MvPolynomial
