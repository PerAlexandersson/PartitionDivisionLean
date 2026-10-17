/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import PartitionDivision.Macdonald.GBasis

/-!
# The finite `(q, t)` pairing

On the symmetric polynomials of degree `n` in the alphabet `σ`, the `(q, t)` scalar product of
Macdonald VI (2.20) is the bilinear form with `⟨g_μ, m_ν⟩ = δ_{μν}`, where the `g_μ` are the basis
of `PartitionDivision/Macdonald/GBasis.lean` and the `m_ν` are the monomial symmetric polynomials.
It is defined here over any commutative ring in which the `g_μ` form a basis, i.e. whenever the
transition determinant is a unit; `MvPolynomial.isUnit_det_macdonaldGFamily_of_injective`
provides this for generic `q, t`.

The form is symmetric because `⟨g_μ, g_ν⟩` is the `(μ, ν)` entry of the transition matrix from the
`g` to the `m`, and that matrix is symmetric: its entries are the coefficients of the kernel
`∏_{i,j} f(xᵢ yⱼ)`, a sum over contingency tables that is invariant under transposition.  It is
nondegenerate because it is the identity matrix in the pair of bases `(g, m)`.

## Main definitions

* `MvPolynomial.macdonaldPairing h`: the bilinear form with `⟨g_μ, m_ν⟩ = δ_{μν}`.

## Main results

* `MvPolynomial.macdonaldPairing_macdonaldGFamily_msymmBasis`: `⟨g_μ, m_ν⟩ = δ_{μν}`.
* `MvPolynomial.eq_macdonaldPairing`: it is the only bilinear form with this property.
* `MvPolynomial.macdonaldPairing_macdonaldGFamily`: `⟨g_μ, g_ν⟩ = [m_μ] g_ν`.
* `MvPolynomial.isSymm_macdonaldPairing`: the form is symmetric.
* `MvPolynomial.nondegenerate_macdonaldPairing`: the form is nondegenerate.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter VI,
  (2.20)--(2.21).
-/

@[expose] public section

open Finset TauCeti Module

namespace MvPolynomial

variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ} {q t : R}
  (h : IsUnit ((msymmBasis σ R n).det (macdonaldGFamily σ q t n)))

/-- **The `(q, t)` pairing** on the symmetric polynomials of degree `n` (Macdonald VI (2.20)): the
bilinear form with `⟨g_μ, m_ν⟩ = δ_{μν}`, defined when the `g_μ` form a basis. -/
noncomputable def macdonaldPairing :
    LinearMap.BilinForm R (symmetricHomogeneousSubmodule σ R n) :=
  Matrix.toLinearMap₂ (macdonaldGBasisOfIsUnit h) (msymmBasis σ R n) 1

/-- The pairing in coordinates: `⟨x, y⟩ = ∑_μ (g-coordinate of x at μ) (m-coordinate of y at μ)`. -/
theorem macdonaldPairing_apply (x y : symmetricHomogeneousSubmodule σ R n) :
    macdonaldPairing h x y =
      ∑ μ, (macdonaldGBasisOfIsUnit h).repr x μ * (msymmBasis σ R n).repr y μ := by
  rw [macdonaldPairing, Matrix.toLinearMap₂_apply]
  simp [Matrix.one_apply]

/-- **`⟨g_μ, m_ν⟩ = δ_{μν}`**, the defining property of the pairing. -/
theorem macdonaldPairing_macdonaldGFamily_msymmBasis
    (μ ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    macdonaldPairing h (macdonaldGFamily σ q t n μ) (msymmBasis σ R n ν) =
      if μ = ν then 1 else 0 := by
  rw [← coe_macdonaldGBasisOfIsUnit h, macdonaldPairing, Matrix.toLinearMap₂_apply_basis,
    Matrix.one_apply]

/-- **Uniqueness**: a bilinear form with `⟨g_μ, m_ν⟩ = δ_{μν}` is
`MvPolynomial.macdonaldPairing`. -/
theorem eq_macdonaldPairing (B : LinearMap.BilinForm R (symmetricHomogeneousSubmodule σ R n))
    (hB : ∀ μ ν, B (macdonaldGFamily σ q t n μ) (msymmBasis σ R n ν) = if μ = ν then 1 else 0) :
    B = macdonaldPairing h :=
  LinearMap.ext_basis (macdonaldGBasisOfIsUnit h) (msymmBasis σ R n) fun μ ν ↦ by
    rw [coe_macdonaldGBasisOfIsUnit, hB, macdonaldPairing_macdonaldGFamily_msymmBasis]

/-- **The Gram matrix of the `g`**: `⟨g_μ, g_ν⟩` is the coordinate of `g_ν` at `m_μ`, the `(μ, ν)`
entry of the transition matrix from the `g` to the monomial basis. -/
theorem macdonaldPairing_macdonaldGFamily
    (μ ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    macdonaldPairing h (macdonaldGFamily σ q t n μ) (macdonaldGFamily σ q t n ν) =
      (msymmBasis σ R n).toMatrix (macdonaldGFamily σ q t n) μ ν := by
  rw [macdonaldPairing_apply, ← coe_macdonaldGBasisOfIsUnit h, Basis.repr_self,
    Basis.toMatrix_apply, coe_macdonaldGBasisOfIsUnit]
  simp [Finsupp.single_apply]

/-- **The `(q, t)` pairing is symmetric**: on the basis `g` it is the transition matrix to the
monomial basis, which is symmetric (`MvPolynomial.isSymm_msymmBasis_toMatrix_macdonaldGFamily`). -/
theorem isSymm_macdonaldPairing : LinearMap.BilinForm.IsSymm (macdonaldPairing h) := by
  refine LinearMap.BilinForm.isSymm_iff_flip.mpr
    (LinearMap.ext_basis (macdonaldGBasisOfIsUnit h) (macdonaldGBasisOfIsUnit h) fun μ ν ↦ ?_)
  rw [LinearMap.BilinForm.flip_apply, coe_macdonaldGBasisOfIsUnit,
    macdonaldPairing_macdonaldGFamily, macdonaldPairing_macdonaldGFamily,
    (isSymm_msymmBasis_toMatrix_macdonaldGFamily q t).apply]

/-- **The `(q, t)` pairing is nondegenerate**: pairing against `m_ν` reads the `g`-coordinate at
`ν`, and pairing against `g_μ` reads the `m`-coordinate at `μ`. -/
theorem nondegenerate_macdonaldPairing :
    LinearMap.BilinForm.Nondegenerate (macdonaldPairing h) := by
  refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · refine (macdonaldGBasisOfIsUnit h).forall_coord_eq_zero_iff.mp fun μ ↦ ?_
    have := hx (msymmBasis σ R n μ)
    rw [macdonaldPairing_apply] at this
    simpa [Basis.repr_self, Finsupp.single_apply] using this
  · refine (msymmBasis σ R n).forall_coord_eq_zero_iff.mp fun μ ↦ ?_
    have := hy (macdonaldGBasisOfIsUnit h μ)
    rw [macdonaldPairing_apply] at this
    simpa [-coe_macdonaldGBasisOfIsUnit, Basis.repr_self, Finsupp.single_apply] using this

end MvPolynomial
