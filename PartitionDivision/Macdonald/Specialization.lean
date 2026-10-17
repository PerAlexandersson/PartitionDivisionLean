/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Macdonald.LexUnitriangular
public import PartitionDivision.Macdonald.PieriCoefficient
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Specializing a regular lex-unitriangular family

Let `φ : R →+* F` be a ring homomorphism from a domain to a field, and let
`O = R_(ker φ)` be the local ring at its kernel.  The ring `O` embeds in `K = Frac R`, and `φ`
extends to `specializationHom φ : O →+* F`.

* A generic row-pair Pieri coefficient at `(q, t) ∈ R × R` lies in `O` as soon as its
  denominator does not vanish at `(φ q, φ t)`: `pieriCoefficientLift`, with its images in `K`
  and in `F`.
* A family over `K` whose members have coefficients in `O` (`regularLift`) specializes along
  every ring map out of `O`, preserving lex-unitriangularity
  (`isLexUnitriangular_specializeFamily`) and every identity of the form
  `e_r * P_λ = Σ c_j • P_{μ_j}` with coefficients in `O` (`esymm_mul_map_eq_sum_smul`).
* For a field `L`, `rootSpecialization ζ` is the map `ℚ[q, t] → L(v)` with `q ↦ ζ`, `t ↦ ζ v`.
  Every Pieri denominator survives it (`pieriDen_rootSpecialization_ne_zero`): each factor is
  `1 - ζ ^ a (ζ v) ^ b` with `b ≥ 1`.  No hypothesis on `ζ` is needed for this.

The regularity input itself is `mem_range_map_of_isLexUnitriangular`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace PartitionDivision.Macdonald

open MvPolynomial Nat.PartitionVector Nat.PartitionVector.Pieri

attribute [local instance] RingHom.ker_isPrime

variable {N : ℕ}

section LocalRing

variable {R F : Type*} [CommRing R] [Field F] (φ : R →+* F)

/-- Elements outside the kernel of a map to a field become units. -/
theorem isUnit_of_mem_primeCompl_ker (y : (RingHom.ker φ).primeCompl) : IsUnit (φ y) := by
  have hy := y.2
  rw [Ideal.mem_primeCompl_iff, RingHom.mem_ker] at hy
  exact isUnit_iff_ne_zero.mpr hy

/-- The extension of `φ` to the local ring at its kernel. -/
def specializationHom : Localization.AtPrime (RingHom.ker φ) →+* F :=
  IsLocalization.lift (M := (RingHom.ker φ).primeCompl) (isUnit_of_mem_primeCompl_ker φ)

/-- The specialization map extends `φ`. -/
@[simp]
theorem specializationHom_algebraMap (x : R) :
    specializationHom φ (algebraMap R (Localization.AtPrime (RingHom.ker φ)) x) = φ x :=
  IsLocalization.lift_eq _ x

/-- The local ring at the kernel embeds in the fraction field. -/
theorem algebraMap_localization_fractionRing_injective [IsDomain R] :
    Function.Injective
      (algebraMap (Localization.AtPrime (RingHom.ker φ)) (FractionRing R)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨⟨x, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (RingHom.ker φ).primeCompl a
  have hspec := congrArg (algebraMap (Localization.AtPrime (RingHom.ker φ)) (FractionRing R))
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker φ)) x s)
  rw [map_mul, ha, zero_mul, ← IsScalarTower.algebraMap_apply] at hspec
  have hx : x = 0 :=
    IsFractionRing.injective R (FractionRing R) (by rw [← hspec, map_zero])
  simp [hx, IsLocalization.mk'_zero]

variable (q t : R)

/-- A Pieri denominator whose specialization is nonzero lies outside the kernel. -/
theorem pieriDen_mem_primeCompl {lam : Nat.PartitionVector N} {δ : Strip N}
    (hden : pieriDen lam δ (φ q) (φ t) ≠ 0) :
    pieriDen lam δ q t ∈ (RingHom.ker φ).primeCompl := by
  rw [Ideal.mem_primeCompl_iff, RingHom.mem_ker, map_pieriDen]
  exact hden

/-- The generic row-pair Pieri coefficient at `(q, t)`, as an element of the local ring at the
kernel of `φ`. -/
def pieriCoefficientLift (lam : Nat.PartitionVector N) (δ : Strip N)
    (hden : pieriDen lam δ (φ q) (φ t) ≠ 0) : Localization.AtPrime (RingHom.ker φ) :=
  IsLocalization.mk' _ (pieriNum lam δ q t) ⟨_, pieriDen_mem_primeCompl φ q t hden⟩

/-- In the fraction field, the lifted Pieri coefficient is the generic Pieri quotient. -/
theorem algebraMap_pieriCoefficientLift [IsDomain R] (lam : Nat.PartitionVector N) (δ : Strip N)
    (hden : pieriDen lam δ (φ q) (φ t) ≠ 0) :
    algebraMap (Localization.AtPrime (RingHom.ker φ)) (FractionRing R)
        (pieriCoefficientLift φ q t lam δ hden) =
      pieriNum lam δ (algebraMap R (FractionRing R) q) (algebraMap R (FractionRing R) t) /
        pieriDen lam δ (algebraMap R (FractionRing R) q) (algebraMap R (FractionRing R) t) := by
  have hne : pieriDen lam δ q t ≠ 0 := by
    intro h
    apply hden
    rw [← map_pieriDen, h, map_zero]
  have hspec := congrArg (algebraMap (Localization.AtPrime (RingHom.ker φ)) (FractionRing R))
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker φ)) (pieriNum lam δ q t)
      ⟨_, pieriDen_mem_primeCompl φ q t hden⟩)
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hspec
  rw [← map_pieriNum, ← map_pieriDen, eq_div_iff
    ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hne)]
  exact hspec

/-- Under the specialization map, the lifted Pieri coefficient is the specialized Pieri
quotient. -/
theorem specializationHom_pieriCoefficientLift (lam : Nat.PartitionVector N) (δ : Strip N)
    (hden : pieriDen lam δ (φ q) (φ t) ≠ 0) :
    specializationHom φ (pieriCoefficientLift φ q t lam δ hden) =
      pieriNum lam δ (φ q) (φ t) / pieriDen lam δ (φ q) (φ t) := by
  have hspec := congrArg (specializationHom φ)
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker φ)) (pieriNum lam δ q t)
      ⟨_, pieriDen_mem_primeCompl φ q t hden⟩)
  rw [map_mul, specializationHom_algebraMap, specializationHom_algebraMap] at hspec
  rw [← map_pieriNum, ← map_pieriDen, eq_div_iff (by rwa [map_pieriDen])]
  exact hspec

end LocalRing

section Family

variable {O K F : Type*} [CommRing O] [CommRing K] [CommRing F] [Algebra O K]
  {P : Nat.PartitionVector N → MvPolynomial (Fin N) K}

/-- The coefficientwise preimage over `O` of a member of a regular lex-unitriangular family. -/
def regularLift (hinj : Function.Injective (algebraMap O K))
    (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hmul : ∀ (r : ℕ) (lam : Nat.PartitionVector N),
      esymm (Fin N) K r * P lam ∈ Submodule.span O (Set.range P))
    (lam : Nat.PartitionVector N) : MvPolynomial (Fin N) O :=
  (mem_range_map_of_isLexUnitriangular hinj hP hmul lam).choose

/-- The preimage maps back to the original family member. -/
@[simp]
theorem map_regularLift (hinj : Function.Injective (algebraMap O K))
    (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hmul : ∀ (r : ℕ) (lam : Nat.PartitionVector N),
      esymm (Fin N) K r * P lam ∈ Submodule.span O (Set.range P))
    (lam : Nat.PartitionVector N) :
    map (algebraMap O K) (regularLift hinj hP hmul lam) = P lam :=
  (mem_range_map_of_isLexUnitriangular hinj hP hmul lam).choose_spec

/-- The preimage family is lex-unitriangular over `O`. -/
theorem isLexUnitriangular_regularLift (hinj : Function.Injective (algebraMap O K))
    (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hmul : ∀ (r : ℕ) (lam : Nat.PartitionVector N),
      esymm (Fin N) K r * P lam ∈ Submodule.span O (Set.range P))
    (lam : Nat.PartitionVector N) :
    IsLexUnitriangular (regularLift hinj hP hmul lam) lam :=
  IsLexUnitriangular.of_map hinj (by rw [map_regularLift]; exact hP lam)

/-- The specialization of a regular lex-unitriangular family along `f : O →+* F`. -/
def specializeFamily (hinj : Function.Injective (algebraMap O K))
    (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hmul : ∀ (r : ℕ) (lam : Nat.PartitionVector N),
      esymm (Fin N) K r * P lam ∈ Submodule.span O (Set.range P))
    (f : O →+* F) (lam : Nat.PartitionVector N) : MvPolynomial (Fin N) F :=
  map f (regularLift hinj hP hmul lam)

/-- The specialized family is lex-unitriangular. -/
theorem isLexUnitriangular_specializeFamily (hinj : Function.Injective (algebraMap O K))
    (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hmul : ∀ (r : ℕ) (lam : Nat.PartitionVector N),
      esymm (Fin N) K r * P lam ∈ Submodule.span O (Set.range P))
    (f : O →+* F) (lam : Nat.PartitionVector N) :
    IsLexUnitriangular (specializeFamily hinj hP hmul f lam) lam :=
  (isLexUnitriangular_regularLift hinj hP hmul lam).map f

/-- An identity `e_r * q = Σ c_j • g_j` whose image in `K` holds, with coefficients in `O`,
specializes along every ring map out of `O`. -/
theorem esymm_mul_map_eq_sum_smul (hinj : Function.Injective (algebraMap O K))
    (f : O →+* F) {J : Type*} (s : Finset J) (r : ℕ) (q : MvPolynomial (Fin N) O)
    (c : J → O) (g : J → MvPolynomial (Fin N) O)
    (h : esymm (Fin N) K r * map (algebraMap O K) q =
      ∑ j ∈ s, algebraMap O K (c j) • map (algebraMap O K) (g j)) :
    esymm (Fin N) F r * map f q = ∑ j ∈ s, f (c j) • map f (g j) := by
  have hO : esymm (Fin N) O r * q = ∑ j ∈ s, c j • g j := by
    apply map_injective _ hinj
    simp only [map_mul, map_esymm, map_sum, smul_eq_C_mul, map_C]
    rw [h]
    simp only [smul_eq_C_mul]
  have hF := congrArg (map f) hO
  simpa only [map_mul, map_esymm, map_sum, smul_eq_C_mul, map_C] using hF

end Family

section RootSpecialization

open scoped Polynomial

variable {L : Type*} [Field L]

/-- At `q = ζ` and `t = ζ X`, every Pieri denominator evaluates to one at zero. -/
theorem eval_zero_pieriDen_C_C_mul_X (ζ : L) (lam : Nat.PartitionVector N) (δ : Strip N) :
    (pieriDen lam δ (Polynomial.C ζ) (Polynomial.C ζ * Polynomial.X) : L[X]).eval 0 = 1 := by
  rw [pieriDen, Polynomial.eval_prod]
  apply Finset.prod_eq_one
  intro ij hij
  have hb := (rowDistance_pos hij).ne'
  simp [pairDen, binomial, hb]

/-- The Pieri denominator is nonzero at `q = ζ`, `t = ζ X`, for every `ζ`. -/
theorem pieriDen_C_C_mul_X_ne_zero (ζ : L) (lam : Nat.PartitionVector N) (δ : Strip N) :
    pieriDen lam δ (Polynomial.C ζ) (Polynomial.C ζ * Polynomial.X) ≠ (0 : L[X]) := by
  intro h
  have := eval_zero_pieriDen_C_C_mul_X ζ lam δ
  rw [h, Polynomial.eval_zero] at this
  exact zero_ne_one this

variable [CharZero L]

/-- The specialization `q ↦ ζ`, `t ↦ ζ v` from `ℚ[q, t]` to `L(v) = Frac L[v]`. -/
def rootSpecialization (ζ : L) : MvPolynomial (Fin 2) ℚ →+* FractionRing L[X] :=
  eval₂Hom ((algebraMap L[X] (FractionRing L[X])).comp (Polynomial.C.comp (Rat.castHom L)))
    ![algebraMap L[X] (FractionRing L[X]) (Polynomial.C ζ),
      algebraMap L[X] (FractionRing L[X]) (Polynomial.C ζ) *
        algebraMap L[X] (FractionRing L[X]) Polynomial.X]

/-- The root specialization sends `q` to `ζ`. -/
@[simp]
theorem rootSpecialization_X_zero (ζ : L) :
    rootSpecialization ζ (MvPolynomial.X 0) =
      algebraMap L[X] (FractionRing L[X]) (Polynomial.C ζ) := by
  simp [rootSpecialization]

/-- The root specialization sends `t` to `ζ v`. -/
@[simp]
theorem rootSpecialization_X_one (ζ : L) :
    rootSpecialization ζ (MvPolynomial.X 1) =
      algebraMap L[X] (FractionRing L[X]) (Polynomial.C ζ) *
        algebraMap L[X] (FractionRing L[X]) Polynomial.X := by
  simp [rootSpecialization]

/-- Every Pieri denominator survives the root specialization. -/
theorem pieriDen_rootSpecialization_ne_zero (ζ : L) (lam : Nat.PartitionVector N)
    (δ : Strip N) :
    pieriDen lam δ (rootSpecialization ζ (MvPolynomial.X 0))
      (rootSpecialization ζ (MvPolynomial.X 1)) ≠ 0 := by
  rw [rootSpecialization_X_zero, rootSpecialization_X_one, ← map_mul, ← map_pieriDen]
  exact (map_ne_zero_iff _ (IsFractionRing.injective L[X] (FractionRing L[X]))).mpr
    (pieriDen_C_C_mul_X_ne_zero ζ lam δ)

end RootSpecialization

end PartitionDivision.Macdonald
