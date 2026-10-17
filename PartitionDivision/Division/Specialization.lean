/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Division.Factorization
public import PartitionDivision.Macdonald.Specialization

/-!
# Specialized Pieri bases

This file is the abstract specialization step of `docs/PIERI.md`, Section 2.  Let `R` be a
domain with fraction field `K`, let `q t : R`, and let `φ : R →+* F` be a map to a field such
that every row-pair Pieri denominator survives at `(φ q, φ t)`.  Assume a family `P` of
polynomials over `K` such that

* (U) each `P λ` is lex-unitriangular (`IsLexUnitriangular`), and
* (P) `P` satisfies the generic vertical Pieri rule at `(q, t)` (`SatisfiesPolynomialPieri`).

Both are explicit hypotheses here; the Macdonald layer is meant to supply them.  Then every
`P λ` has coefficients in the local ring at `ker φ`, and specializing gives a basis
`specializedBasis` of the symmetric polynomials over `F` with

* `specializedBasis_zero`: the basis vector at `0` is `1`;
* `satisfiesPieri_specializedBasis`: `SatisfiesPieri` at `(φ q, φ t)`.

`satisfiesPieri_rootSpecialization` instantiates this at `q ↦ ζ`, `t ↦ ζ v`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace PartitionDivision

open MvPolynomial Nat.PartitionVector Nat.PartitionVector.Pieri Macdonald

attribute [local instance] RingHom.ker_isPrime

variable {N : ℕ}

/-- The generic vertical Pieri rule for a family of polynomials over a field, with the row-pair
coefficients evaluated at `(q, t)`.  Strips leaving the `N` rows do not occur, since a strip is a
function on the `N` rows. -/
def SatisfiesPolynomialPieri {K : Type*} [Field K]
    (P : Nat.PartitionVector N → MvPolynomial (Fin N) K) (q t : K) : Prop := by
  classical
  exact ∀ (r : ℕ) (lam : Nat.PartitionVector N),
    esymm (Fin N) K r * P lam =
      ∑ δ : Strip N,
        if IsLegal lam δ ∧ stripWeight δ = r then
          pieriCoefficient q t lam δ • P (addStrip lam δ)
        else 0

section General

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] (φ : R →+* F) (q t : R)
  (hden : ∀ (lam : Nat.PartitionVector N) (δ : Strip N), pieriDen lam δ (φ q) (φ t) ≠ 0)
  {P : Nat.PartitionVector N → MvPolynomial (Fin N) (FractionRing R)}

include hden

omit [IsDomain R] in
/-- The Pieri coefficient of `(r, λ, δ)` as an element of the local ring at `ker φ`; it is zero
when `δ` is not a legal strip of size `r`. -/
def pieriLiftCoeff (r : ℕ) (lam : Nat.PartitionVector N) (δ : Strip N) :
    Localization.AtPrime (RingHom.ker φ) := by
  classical
  exact if IsLegal lam δ ∧ stripWeight δ = r then pieriCoefficientLift φ q t lam δ (hden lam δ)
    else 0

/-- The generic Pieri rule written with coefficients in the local ring at `ker φ`. -/
theorem esymm_mul_eq_sum_pieriLiftCoeff
    (hPieri : SatisfiesPolynomialPieri P (algebraMap R (FractionRing R) q)
      (algebraMap R (FractionRing R) t))
    (r : ℕ) (lam : Nat.PartitionVector N) :
    esymm (Fin N) (FractionRing R) r * P lam =
      ∑ δ : Strip N,
        algebraMap (Localization.AtPrime (RingHom.ker φ)) (FractionRing R)
          (pieriLiftCoeff φ q t hden r lam δ) • P (addStrip lam δ) := by
  rw [hPieri r lam]
  refine Finset.sum_congr rfl fun δ _ ↦ ?_
  unfold pieriLiftCoeff
  split_ifs
  · rw [algebraMap_pieriCoefficientLift, pieriCoefficient]
  · rw [map_zero, zero_smul]

/-- Under the generic Pieri rule, the `O`-span of the family is stable under multiplication by
the elementary symmetric polynomials. -/
theorem esymm_mul_mem_span
    (hPieri : SatisfiesPolynomialPieri P (algebraMap R (FractionRing R) q)
      (algebraMap R (FractionRing R) t))
    (r : ℕ) (lam : Nat.PartitionVector N) :
    esymm (Fin N) (FractionRing R) r * P lam ∈
      Submodule.span (Localization.AtPrime (RingHom.ker φ)) (Set.range P) := by
  rw [esymm_mul_eq_sum_pieriLiftCoeff φ q t hden hPieri]
  refine Submodule.sum_mem _ fun δ _ ↦ ?_
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The specialized basis: the lex-unitriangular family `P`, whose coefficients lie in the local
ring at `ker φ`, specialized along `φ`. -/
def specializedBasis (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hPieri : SatisfiesPolynomialPieri P (algebraMap R (FractionRing R) q)
      (algebraMap R (FractionRing R) t)) :
    Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F) :=
  lexUnitriangularBasis (isLexUnitriangular_specializeFamily
    (algebraMap_localization_fractionRing_injective φ) hP (esymm_mul_mem_span φ q t hden hPieri)
    (specializationHom φ))

/-- The vectors of the specialized basis are the specializations of the regular lifts of `P`. -/
theorem coe_specializedBasis (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hPieri : SatisfiesPolynomialPieri P (algebraMap R (FractionRing R) q)
      (algebraMap R (FractionRing R) t))
    (lam : Nat.PartitionVector N) :
    (specializedBasis φ q t hden hP hPieri lam : MvPolynomial (Fin N) F) =
      map (specializationHom φ) (regularLift (algebraMap_localization_fractionRing_injective φ)
        hP (esymm_mul_mem_span φ q t hden hPieri) lam) := by
  rw [specializedBasis, coe_lexUnitriangularBasis]
  rfl

/-- The specialized basis vector at the empty partition is one. -/
theorem specializedBasis_zero (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hPieri : SatisfiesPolynomialPieri P (algebraMap R (FractionRing R) q)
      (algebraMap R (FractionRing R) t)) :
    specializedBasis φ q t hden hP hPieri 0 = 1 := by
  apply Subtype.ext
  rw [specializedBasis, coe_lexUnitriangularBasis]
  exact (isLexUnitriangular_specializeFamily _ hP _ _ 0).eq_one

/-- **Specialized Pieri rule.**  The specialized basis satisfies the vertical Pieri rule at
`(φ q, φ t)`. -/
theorem satisfiesPieri_specializedBasis (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hPieri : SatisfiesPolynomialPieri P (algebraMap R (FractionRing R) q)
      (algebraMap R (FractionRing R) t)) :
    SatisfiesPieri (specializedBasis φ q t hden hP hPieri) (φ q) (φ t) := by
  intro r lam
  have hinj := algebraMap_localization_fractionRing_injective φ
  have hmul := esymm_mul_mem_span φ q t hden hPieri
  have htrans := esymm_mul_map_eq_sum_smul hinj (specializationHom φ) Finset.univ r
    (regularLift hinj hP hmul lam) (pieriLiftCoeff φ q t hden r lam)
    (fun δ ↦ regularLift hinj hP hmul (addStrip lam δ))
    (by
      simp only [map_regularLift]
      exact esymm_mul_eq_sum_pieriLiftCoeff φ q t hden hPieri r lam)
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, AddSubmonoidClass.coe_finsetSum]
  change esymm (Fin N) F r * _ = _
  rw [coe_specializedBasis, htrans]
  refine Finset.sum_congr rfl fun δ _ ↦ ?_
  unfold pieriLiftCoeff
  split_ifs
  · rw [specializationHom_pieriCoefficientLift, SetLike.val_smul, coe_specializedBasis,
      pieriCoefficient]
  · rw [map_zero, zero_smul, ZeroMemClass.coe_zero]

end General

open scoped Polynomial in
/-- **Root-of-unity specialization.**  For a field `L` of characteristic zero and any `ζ : L`, a
lex-unitriangular family over `ℚ(q, t)` satisfying the generic Pieri rule specializes at
`q = ζ`, `t = ζ v` to a basis of the symmetric polynomials over `L(v)` that satisfies the
vertical Pieri rule at `(ζ, ζ v)` and has `1` at the empty partition. -/
theorem satisfiesPieri_rootSpecialization {L : Type*} [Field L] [CharZero L] (ζ : L)
    {P : Nat.PartitionVector N →
      MvPolynomial (Fin N) (FractionRing (MvPolynomial (Fin 2) ℚ))}
    (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hPieri : SatisfiesPolynomialPieri P
      (algebraMap (MvPolynomial (Fin 2) ℚ) _ (MvPolynomial.X 0))
      (algebraMap (MvPolynomial (Fin 2) ℚ) _ (MvPolynomial.X 1))) :
    SatisfiesPieri
        (specializedBasis (rootSpecialization ζ) (MvPolynomial.X 0) (MvPolynomial.X 1)
          (pieriDen_rootSpecialization_ne_zero ζ) hP hPieri)
        (algebraMap L[X] (FractionRing L[X]) (Polynomial.C ζ))
        (algebraMap L[X] (FractionRing L[X]) (Polynomial.C ζ) *
          algebraMap L[X] (FractionRing L[X]) Polynomial.X) ∧
      specializedBasis (rootSpecialization ζ) (MvPolynomial.X 0) (MvPolynomial.X 1)
          (pieriDen_rootSpecialization_ne_zero ζ) hP hPieri 0 = 1 := by
  rw [← rootSpecialization_X_one, ← rootSpecialization_X_zero]
  exact ⟨satisfiesPieri_specializedBasis _ _ _ _ hP hPieri,
    specializedBasis_zero _ _ _ _ hP hPieri⟩

end PartitionDivision
