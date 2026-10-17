/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import PartitionDivision.Macdonald.GPolynomial
public import PartitionDivision.TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basis
public import PartitionDivision.TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.HsymmPart

/-!
# The `g` basis of the symmetric homogeneous polynomials

For partitions `ν` of `n` with at most `|σ|` parts, the polynomials `g_ν(x; q, t)` of
`PartitionDivision/Macdonald/GPolynomial.lean` form a basis of the symmetric polynomials in `σ`
that are homogeneous of degree `n`, for generic `q` and `t` (Macdonald VI (2.19)).

## The argument

Write the family in the monomial basis `TauCeti.msymmBasis`.  The entries of the transition matrix
are the kernel coefficients `[x^μ] g_ν`; it is symmetric
(`MvPolynomial.isSymm_msymmBasis_toMatrix_macdonaldGFamily`).  Its determinant commutes with every
ring homomorphism under which the denominators `1 - q^{i+1}` stay units
(`MvPolynomial.map_det_macdonaldGFamily`).  At `q = t = 0` the family is `h_ν`, and
`h_ν = ∑_μ K_{μν} s_μ` with the Kostka matrix unitriangular for the lexicographic order, so the
determinant is a unit over every commutative ring
(`MvPolynomial.isUnit_det_macdonaldGFamily_zero_zero`).

For generic parameters we pass through the localization `L` of `ℚ[q, t]` at the polynomials with
nonzero constant term.  In `L` every `1 - q^{i+1}` is a unit; `L` maps to `ℚ` by `q, t ↦ 0`, where
the determinant becomes the unit above, so the determinant over `L` is nonzero; and `L` embeds into
every field `K` receiving an injective ring homomorphism `φ : ℚ[q, t] → K`, so the determinant over
`K` with `q = φ q`, `t = φ t` is nonzero (`MvPolynomial.isUnit_det_macdonaldGFamily_of_injective`).
Taking `K = FractionRing ℚ[q, t]` gives the basis over `ℚ(q, t)`
(`MvPolynomial.isUnit_det_macdonaldGFamily_fractionRing`).

## Main definitions

* `MvPolynomial.macdonaldGFamily σ q t n`: the `g_ν` as elements of
  `TauCeti.symmetricHomogeneousSubmodule σ R n`, indexed like the monomial and Schur bases.
* `MvPolynomial.macdonaldGBasisOfIsUnit`: the basis obtained when the transition determinant is a
  unit, over any commutative ring.
* `MvPolynomial.macdonaldGBasis σ n φ hφ`: the basis over a field `K` with algebraically
  independent `q = φ q`, `t = φ t`, given as an injective ring homomorphism `φ : ℚ[q, t] → K`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter VI,
  (2.19), and Chapter I, Section 6 for `h_ν = ∑_μ K_{μν} s_μ`.
-/

@[expose] public section

open Finset TauCeti Module

namespace MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {n : ℕ}

section Basis

/-- `g_μ` lies in the symmetric polynomials of degree `|μ|`. -/
theorem macdonaldGPart_mem_symmetricHomogeneousSubmodule (q t : R) (μ : n.Partition) :
    macdonaldGPart σ q t μ ∈ symmetricHomogeneousSubmodule σ R n :=
  mem_symmetricHomogeneousSubmodule.mpr
    ⟨macdonaldGPart_isSymmetric q t μ, isHomogeneous_macdonaldGPart q t μ⟩

variable (σ) in
/-- **The family `g_ν`** of the partitions `ν` of `n` with at most `|σ|` parts, as elements of the
symmetric polynomials of degree `n`.  It is indexed like `TauCeti.msymmBasis` and
`TauCeti.schurPolyBasis`. -/
noncomputable def macdonaldGFamily (q t : R) (n : ℕ)
    (ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    symmetricHomogeneousSubmodule σ R n :=
  ⟨macdonaldGPart σ q t ν.1, macdonaldGPart_mem_symmetricHomogeneousSubmodule q t ν.1⟩

/-- The vectors of `MvPolynomial.macdonaldGFamily` are the polynomials `g_ν`. -/
@[simp]
theorem coe_macdonaldGFamily (q t : R) (ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    (macdonaldGFamily σ q t n ν : MvPolynomial σ R) = macdonaldGPart σ q t ν.1 :=
  rfl

/-- **The transition matrix from the `g_ν` to the monomial basis**: its `(μ, ν)` entry, the
coordinate of `g_ν` at `m_μ`, is the kernel coefficient of `x^μ y^ν`. -/
theorem msymmBasis_toMatrix_macdonaldGFamily (q t : R)
    (μ ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
    (msymmBasis σ R n).toMatrix (macdonaldGFamily σ q t n) μ ν =
      macdonaldKernelCoeff q t (partWeight σ ν.1) (partWeight σ μ.1) := by
  rw [Basis.toMatrix_apply, msymmBasis_repr_apply, coe_macdonaldGFamily,
    coeff_macdonaldGPart_partWeight q t ν.1 μ.1 ν.2]

/-- **The transition matrix from the `g_ν` to the monomial basis is symmetric.** -/
theorem isSymm_msymmBasis_toMatrix_macdonaldGFamily (q t : R) :
    ((msymmBasis σ R n).toMatrix (macdonaldGFamily σ q t n)).IsSymm := by
  ext μ ν
  rw [Matrix.transpose_apply, msymmBasis_toMatrix_macdonaldGFamily,
    msymmBasis_toMatrix_macdonaldGFamily, macdonaldKernelCoeff_comm]

/-- **The transition determinant commutes with ring homomorphisms** under which the denominators
`1 - q^{i+1}` are units. -/
theorem map_det_macdonaldGFamily (f : R →+* S) {q : R} (hq : ∀ i, IsUnit (1 - q ^ (i + 1)))
    (t : R) :
    f ((msymmBasis σ R n).det (macdonaldGFamily σ q t n)) =
      (msymmBasis σ S n).det (macdonaldGFamily σ (f q) (f t) n) := by
  rw [Basis.det_apply, Basis.det_apply, RingHom.map_det]
  congr 1
  ext μ ν
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply,
    msymmBasis_repr_apply, msymmBasis_repr_apply, coe_macdonaldGFamily, coe_macdonaldGFamily,
    ← coeff_map, map_macdonaldGPart f hq]

/-- **At `q = t = 0` the transition determinant is a unit**: the family is `h_ν`, whose matrix in
the Schur basis is the transposed Kostka matrix, unitriangular for the lexicographic order, and the
Schur basis is a basis. -/
theorem isUnit_det_macdonaldGFamily_zero_zero :
    IsUnit ((msymmBasis σ R n).det (macdonaldGFamily σ (0 : R) 0 n)) := by
  classical
  cases subsingleton_or_nontrivial R
  · exact isUnit_of_subsingleton _
  set b := schurPolyBasis σ R n
  have hexp (ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
      macdonaldGFamily σ (0 : R) 0 n ν = ∑ μ, (kostkaNumber μ.1 ν.1 : R) • b μ := by
    refine Subtype.ext ?_
    rw [coe_macdonaldGFamily, macdonaldGPart_zero_zero,
      hsymmPart_eq_sum_kostkaNumber_smul_schurPoly, Submodule.coe_sum,
      ← Fintype.sum_subtype_add_sum_subtype (fun μ : n.Partition ↦ μ.parts.card ≤ Fintype.card σ)]
    have hzero : ∑ μ : {μ : n.Partition // ¬μ.parts.card ≤ Fintype.card σ},
        (kostkaNumber μ.1 ν.1 : R) • schurPoly σ R μ.1 = 0 :=
      Finset.sum_eq_zero fun μ _ ↦ by
        rw [(schurPoly_eq_zero_iff μ.1).mpr (by
          rw [YoungDiagram.colLen_zero_ofPartition]; exact not_le.mp μ.2), smul_zero]
    rw [hzero, add_zero]
    exact sum_congr rfl fun μ _ ↦ by simp [b]
  have hentry (μ ν : {ν : n.Partition // ν.parts.card ≤ Fintype.card σ}) :
      b.toMatrix (macdonaldGFamily σ (0 : R) 0 n) μ ν = (kostkaNumber μ.1 ν.1 : R) := by
    rw [Basis.toMatrix_apply, hexp, b.repr_sum_self]
  rw [Basis.det_apply, ← Basis.toMatrix_mul_toMatrix (msymmBasis σ R n) b, Matrix.det_mul]
  refine IsUnit.mul (by rw [← Basis.det_apply]; exact Basis.isUnit_det _ _) ?_
  open scoped PartitionLex in
  have htri : (b.toMatrix (macdonaldGFamily σ (0 : R) 0 n)).IsLowerTriangular := by
    intro μ ν hμν
    have hlt : (μ : n.Partition) < (ν : n.Partition) := Subtype.coe_lt_coe.mpr hμν
    rw [hentry, kostkaNumber_eq_zero_of_not_dominates fun hdom ↦
      absurd (lex_le_of_dominates hdom) (not_le.mpr hlt), Nat.cast_zero]
  rw [Matrix.det_of_isLowerTriangular _ htri]
  simp [hentry, kostkaNumber_self]

/-- **The `g` basis, when the transition determinant is a unit**, over any commutative ring: the
`g_ν` for the partitions `ν` of `n` with at most `|σ|` parts form a basis of the symmetric
polynomials of degree `n`.  Its vectors are read off by
`MvPolynomial.coe_macdonaldGBasisOfIsUnit`. -/
noncomputable def macdonaldGBasisOfIsUnit {q t : R}
    (h : IsUnit ((msymmBasis σ R n).det (macdonaldGFamily σ q t n))) :
    Basis {ν : n.Partition // ν.parts.card ≤ Fintype.card σ} R
      (symmetricHomogeneousSubmodule σ R n) :=
  .mk ((Basis.is_basis_iff_det _).mpr h).1 ((Basis.is_basis_iff_det _).mpr h).2.ge

/-- The vectors of `MvPolynomial.macdonaldGBasisOfIsUnit` are the `g_ν`. -/
@[simp]
theorem coe_macdonaldGBasisOfIsUnit {q t : R}
    (h : IsUnit ((msymmBasis σ R n).det (macdonaldGFamily σ q t n))) :
    ⇑(macdonaldGBasisOfIsUnit h) = macdonaldGFamily σ q t n :=
  Basis.coe_mk _ _

end Basis

section Generic

/-- The polynomials in `q, t` over `ℚ` with nonzero constant coefficient. -/
private noncomputable abbrev constCoeffNeZero : Submonoid (MvPolynomial (Fin 2) ℚ) :=
  (nonZeroDivisors ℚ).comap (constantCoeff : MvPolynomial (Fin 2) ℚ →+* ℚ)

private theorem ne_zero_of_mem_constCoeffNeZero (y : constCoeffNeZero) :
    (y : MvPolynomial (Fin 2) ℚ) ≠ 0 := fun h ↦ by
  have := y.2
  rw [h] at this
  simp at this

/-- **The transition determinant is nonzero for generic `q, t`**: over a field `K` with an
injective ring homomorphism `φ : ℚ[q, t] → K` (that is, `φ q` and `φ t` algebraically independent
over `ℚ`), the determinant of the `g_ν` with `q = φ (X 0)` and `t = φ (X 1)` in the monomial basis
is a unit.  The proof specializes to `q = t = 0` inside the localization of `ℚ[q, t]` at the
polynomials with nonzero constant term. -/
theorem isUnit_det_macdonaldGFamily_of_injective {K : Type*} [Field K]
    (φ : MvPolynomial (Fin 2) ℚ →+* K) (hφ : Function.Injective φ) :
    IsUnit ((msymmBasis σ K n).det (macdonaldGFamily σ (φ (X 0)) (φ (X 1)) n)) := by
  let L := Localization constCoeffNeZero
  set q₀ : L := algebraMap (MvPolynomial (Fin 2) ℚ) L (X 0) with hq₀
  set t₀ : L := algebraMap (MvPolynomial (Fin 2) ℚ) L (X 1) with ht₀
  have hunit (i : ℕ) : IsUnit (1 - q₀ ^ (i + 1)) := by
    have hmem : (1 - X 0 ^ (i + 1) : MvPolynomial (Fin 2) ℚ) ∈ constCoeffNeZero := by
      simp
    simpa using IsLocalization.map_units L (⟨_, hmem⟩ : constCoeffNeZero)
  let ε : L →+* ℚ := IsLocalization.lift (M := constCoeffNeZero) (g := constantCoeff)
    fun y ↦ isUnit_iff_ne_zero.mpr (nonZeroDivisors.ne_zero y.2)
  let ψ : L →+* K := IsLocalization.lift (M := constCoeffNeZero) (g := φ)
    fun y ↦ isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff φ hφ).mpr (ne_zero_of_mem_constCoeffNeZero y))
  have hψ : Function.Injective ψ := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [(IsLocalization.injective L fun y hy ↦
      mem_nonZeroDivisors_of_ne_zero (ne_zero_of_mem_constCoeffNeZero ⟨y, hy⟩)).eq_iff,
      hφ.eq_iff]
  have hε := map_det_macdonaldGFamily (σ := σ) (n := n) ε hunit t₀
  simp only [ε, hq₀, ht₀, IsLocalization.lift_eq, constantCoeff_X] at hε
  have hD : (msymmBasis σ L n).det (macdonaldGFamily σ q₀ t₀ n) ≠ 0 := fun h ↦ by
    have := (isUnit_det_macdonaldGFamily_zero_zero (σ := σ) (R := ℚ) (n := n))
    rw [← hε, h, map_zero] at this
    exact not_isUnit_zero this
  have hψD := map_det_macdonaldGFamily (σ := σ) (n := n) ψ hunit t₀
  simp only [ψ, hq₀, ht₀, IsLocalization.lift_eq] at hψD
  rw [← hψD]
  exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff ψ hψ).mpr hD)

variable (σ n) in
/-- **The `g` basis for generic `q, t`** (Lemma 1 of the Pieri ledger): over a field `K` with an
injective ring homomorphism `φ : ℚ[q, t] → K`, the `g_ν(x; φ q, φ t)` for the partitions `ν` of
`n` with at most `|σ|` parts form a basis of the symmetric polynomials of degree `n`. -/
noncomputable def macdonaldGBasis {K : Type*} [Field K] (φ : MvPolynomial (Fin 2) ℚ →+* K)
    (hφ : Function.Injective φ) :
    Basis {ν : n.Partition // ν.parts.card ≤ Fintype.card σ} K
      (symmetricHomogeneousSubmodule σ K n) :=
  macdonaldGBasisOfIsUnit (isUnit_det_macdonaldGFamily_of_injective φ hφ)

/-- The vectors of `MvPolynomial.macdonaldGBasis` are the `g_ν` with `q = φ (X 0)` and
`t = φ (X 1)`. -/
@[simp]
theorem coe_macdonaldGBasis {K : Type*} [Field K] (φ : MvPolynomial (Fin 2) ℚ →+* K)
    (hφ : Function.Injective φ) :
    ⇑(macdonaldGBasis σ n φ hφ) = macdonaldGFamily σ (φ (X 0)) (φ (X 1)) n :=
  coe_macdonaldGBasisOfIsUnit _

/-- **The transition determinant is a unit over `ℚ(q, t)`**, the fraction field of `ℚ[q, t]`
with `q = X 0` and `t = X 1`. -/
theorem isUnit_det_macdonaldGFamily_fractionRing :
    IsUnit ((msymmBasis σ (FractionRing (MvPolynomial (Fin 2) ℚ)) n).det
      (macdonaldGFamily σ
        (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ)) (X 0))
        (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ)) (X 1)) n)) :=
  isUnit_det_macdonaldGFamily_of_injective _ (IsFractionRing.injective _ _)

end Generic

end MvPolynomial
