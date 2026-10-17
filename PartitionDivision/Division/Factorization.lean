/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Division.TraceIdentity
public import PartitionDivision.Macdonald.PieriCoefficient
public import PartitionDivision.Mathlib.Algebra.Polynomial.RegularQuotient
public import PartitionDivision.Mathlib.RingTheory.MvPolynomial.Symmetric.ElementaryExpansion

/-!
# Conditional root-of-unity factorization

This file derives the factorization needed by the abstract trace identity from a symmetric
basis satisfying the rectangular and Pieri identities.  The Macdonald-specific identities are
kept as explicit hypotheses.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace PartitionDivision

open MvPolynomial Nat.PartitionVector Nat.PartitionVector.Pieri

variable {F : Type*} [Field F] {N k : ℕ}

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The number of boxes in a zero-one strip. -/
def stripWeight (delta : Strip N) : ℕ := ∑ i, (delta i).val

/-- Add a strip when it is legal, and return the original partition otherwise. -/
def addStrip (lam : Nat.PartitionVector N) (delta : Strip N) : Nat.PartitionVector N := by
  classical
  exact if h : IsLegal lam delta then ⟨fun i ↦ lam i + delta i, h⟩ else lam

/-- A legal strip is added coordinatewise. -/
@[simp]
theorem addStrip_apply_of_legal {lam : Nat.PartitionVector N} {delta : Strip N}
    (hdelta : IsLegal lam delta) (i : Fin N) : addStrip lam delta i = lam i + delta i := by
  simp [addStrip, hdelta]

/-- Adding a legal strip and then a rectangle can be done in the opposite order. -/
theorem addStrip_addRectangle {lam : Nat.PartitionVector N} {delta : Strip N}
    (hdelta : IsLegal lam delta) (a h : ℕ) :
    addStrip (addRectangle lam a h) delta = addRectangle (addStrip lam delta) a h := by
  apply Nat.PartitionVector.ext
  intro i
  simp [addStrip_apply_of_legal hdelta, addStrip_apply_of_legal (hdelta.addRectangle a h),
    addRectangle_apply, add_left_comm, add_comm]

/-- The row-pair Pieri coefficient specialized to two field elements. -/
def pieriCoefficient (zeta t : F) (lam : Nat.PartitionVector N) (delta : Strip N) : F :=
  pieriNum lam delta zeta t / pieriDen lam delta zeta t

/-- The elementary symmetric polynomial after raising every variable to its `k`th power. -/
def expandedEsymm (k i : ℕ) : MvPolynomial (Fin N) F :=
  expand k (esymm (Fin N) F i)

/-- The elementary symmetric polynomial as an element of the symmetric subalgebra. -/
def symmetricEsymm (r : ℕ) : symmetricSubalgebra (Fin N) F :=
  ⟨esymm (Fin N) F r, esymm_isSymmetric (Fin N) F r⟩

/-- The expanded elementary symmetric polynomial as an element of the symmetric subalgebra. -/
def symmetricExpandedEsymm (k i : ℕ) : symmetricSubalgebra (Fin N) F :=
  ⟨expandedEsymm k i, (esymm_isSymmetric (Fin N) F i).expand k⟩

/-- The linear shift operator determined by adding a rectangle to every basis index. -/
def basisShift
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (k h : ℕ) :
    symmetricSubalgebra (Fin N) F →ₗ[F] symmetricSubalgebra (Fin N) F :=
  P.constr F fun lam ↦ P (addRectangle lam k h)

/-- The basis shift has its prescribed value on every basis vector. -/
@[simp]
theorem basisShift_apply_basis
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (k h : ℕ) (lam : Nat.PartitionVector N) :
    basisShift P k h (P lam) = P (addRectangle lam k h) := by
  exact P.constr_basis F _ lam

/-- A convenient all-strips formulation of the vertical Pieri rule. -/
def SatisfiesPieri
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (zeta t : F) : Prop := by
  classical
  exact ∀ (r : ℕ) (lam : Nat.PartitionVector N),
      symmetricEsymm r * P lam =
        ∑ delta : Strip N,
          if IsLegal lam delta ∧ stripWeight delta = r then
            pieriCoefficient zeta t lam delta • P (addStrip lam delta)
          else 0

/-- The rectangular specialization required of the symmetric basis. -/
def SatisfiesRectangles
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (k : ℕ) : Prop :=
  ∀ h, 1 ≤ h → h ≤ N → P (k • prefixOnes h) = symmetricExpandedEsymm k h

/-- Inherited legal strips have the same specialized Pieri coefficient after a rectangle. -/
theorem pieriCoefficient_addRectangle_eq (zeta t : F) (hzeta : zeta ^ k = 1)
    {lam : Nat.PartitionVector N} {delta : Strip N} (hdelta : IsLegal lam delta) (h : ℕ) :
    pieriCoefficient zeta t (addRectangle lam k h) delta =
      pieriCoefficient zeta t lam delta := by
  rw [pieriCoefficient, pieriCoefficient, pieriNum_addRectangle_eq zeta t hzeta hdelta h,
    pieriDen_addRectangle_eq zeta t hzeta hdelta h]

/-- A strip made legal by a rectangle has zero specialized Pieri coefficient. -/
theorem pieriCoefficient_addRectangle_eq_zero_of_not_legal (zeta t : F)
    (hzeta : zeta ^ k = 1) {lam : Nat.PartitionVector N} {delta : Strip N} {h : ℕ}
    (hh : 1 ≤ h) (hshift : IsLegal (addRectangle lam k h) delta)
    (hbad : ¬IsLegal lam delta) :
    pieriCoefficient zeta t (addRectangle lam k h) delta = 0 := by
  rw [pieriCoefficient,
    pieriNum_addRectangle_eq_zero_of_not_legal zeta t hzeta hh hshift hbad, zero_div]

/-- Left multiplication inside the symmetric subalgebra, as a linear map. -/
def symmetricMul (a : symmetricSubalgebra (Fin N) F) :
    symmetricSubalgebra (Fin N) F →ₗ[F] symmetricSubalgebra (Fin N) F where
  toFun f := a * f
  map_add' f g := by simp [mul_add]
  map_smul' c f := by
    simp only [Algebra.smul_def]
    ac_rfl

/-- Evaluation of left multiplication in the symmetric subalgebra. -/
@[simp]
theorem symmetricMul_apply (a f : symmetricSubalgebra (Fin N) F) :
    symmetricMul a f = a * f := rfl

/-- The basis shift commutes with multiplication by every elementary symmetric polynomial. -/
theorem basisShift_symmetricEsymm_mul
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (zeta t : F) (hzeta : zeta ^ k = 1) (hPieri : SatisfiesPieri P zeta t)
    {h : ℕ} (hh : 1 ≤ h) (r : ℕ) (f : symmetricSubalgebra (Fin N) F) :
    basisShift P k h (symmetricEsymm r * f) =
      symmetricEsymm r * basisShift P k h f := by
  classical
  have hmaps :
      (basisShift P k h).comp (symmetricMul (symmetricEsymm r)) =
        (symmetricMul (symmetricEsymm r)).comp (basisShift P k h) := by
    apply P.ext
    intro lam
    simp only [LinearMap.comp_apply, symmetricMul_apply, basisShift_apply_basis]
    rw [hPieri r lam, map_sum, hPieri r (addRectangle lam k h)]
    apply Finset.sum_congr rfl
    intro delta _
    by_cases hweight : stripWeight delta = r
    · by_cases hlegal : IsLegal lam delta
      · have hshift : IsLegal (addRectangle lam k h) delta :=
          hlegal.addRectangle k h
        simp [hweight, hlegal, hshift,
          pieriCoefficient_addRectangle_eq zeta t hzeta hlegal h,
          addStrip_addRectangle hlegal]
      · by_cases hshift : IsLegal (addRectangle lam k h) delta
        · simp [hweight, hlegal, hshift,
            pieriCoefficient_addRectangle_eq_zero_of_not_legal zeta t hzeta hh hshift hlegal]
        · simp [hweight, hlegal, hshift]
    · simp [hweight]
  exact LinearMap.congr_fun hmaps f

/-- Adding a rectangle to the zero partition gives the corresponding rectangular partition. -/
@[simp]
theorem addRectangle_zero (a h : ℕ) :
    addRectangle (0 : Nat.PartitionVector N) a h = a • prefixOnes h := by
  apply Nat.PartitionVector.ext
  intro i
  simp [addRectangle_apply]

/-- Under the elementary-symmetric equivalence, a variable is the corresponding elementary
symmetric polynomial. -/
theorem esymmAlgEquiv_X (i : Fin N) :
    MvPolynomial.esymmAlgEquiv (Fin N) F (by simp) (X i) = symmetricEsymm (i + 1) := by
  apply Subtype.ext
  simp [MvPolynomial.esymmAlgEquiv_apply, MvPolynomial.esymmAlgHom_apply, symmetricEsymm]

/-- The shift of one is the expanded elementary symmetric polynomial specified by the
rectangular-basis hypothesis. -/
theorem basisShift_one
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (hzero : P 0 = 1)
    (hrectangle : SatisfiesRectangles P k)
    {h : ℕ} (hh : 1 ≤ h) (hhN : h ≤ N) :
    basisShift P k h 1 = symmetricExpandedEsymm k h := by
  calc
    basisShift P k h 1 = basisShift P k h (P 0) := by rw [hzero]
    _ = P (addRectangle 0 k h) := basisShift_apply_basis P k h 0
    _ = symmetricExpandedEsymm k h := by simpa using hrectangle h hh hhN

/-- Every symmetric polynomial is shifted by multiplication with the expanded elementary
symmetric polynomial. -/
theorem basisShift_eq_symmetricExpandedEsymm_mul
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (zeta t : F) (hzeta : zeta ^ k = 1) (hPieri : SatisfiesPieri P zeta t)
    (hzero : P 0 = 1)
    (hrectangle : SatisfiesRectangles P k)
    {h : ℕ} (hh : 1 ≤ h) (hhN : h ≤ N)
    (f : symmetricSubalgebra (Fin N) F) :
    basisShift P k h f = symmetricExpandedEsymm k h * f := by
  let e : MvPolynomial (Fin N) F ≃ₐ[F] symmetricSubalgebra (Fin N) F :=
    MvPolynomial.esymmAlgEquiv (Fin N) F (by simp)
  obtain ⟨q, rfl⟩ := e.surjective f
  induction q using MvPolynomial.induction_on with
  | C a =>
      have heC : e (C a) = a • 1 := by
        rw [Algebra.smul_def, mul_one]
        rw [← MvPolynomial.algebraMap_eq]
        exact e.commutes a
      rw [heC]
      change basisShift P k h (a • 1) = symmetricExpandedEsymm k h * (a • 1)
      rw [map_smul, basisShift_one P hzero hrectangle hh hhN]
      simp only [Algebra.smul_def]
      ac_rfl
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq]
      exact (mul_add _ _ _).symm
  | mul_X p i hp =>
      rw [map_mul, esymmAlgEquiv_X, mul_comm,
        basisShift_symmetricEsymm_mul P zeta t hzeta hPieri hh, hp]
      ac_rfl

/-- The basis vector indexed by a rectangular shift factors by the corresponding expanded
elementary symmetric polynomial. -/
theorem basis_addRectangle
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (zeta t : F) (hzeta : zeta ^ k = 1) (hPieri : SatisfiesPieri P zeta t)
    (hzero : P 0 = 1)
    (hrectangle : SatisfiesRectangles P k)
    (lam : Nat.PartitionVector N) {h : ℕ} (hh : 1 ≤ h) (hhN : h ≤ N) :
    P (addRectangle lam k h) = symmetricExpandedEsymm k h * P lam := by
  rw [← basisShift_apply_basis P k h lam]
  exact basisShift_eq_symmetricExpandedEsymm_mul P zeta t hzeta hPieri hzero hrectangle
    hh hhN (P lam)

/-- Reconstruct a partition vector from a finitely supported vector of consecutive
differences. -/
def partitionOfDifferences (d : Fin N →₀ ℕ) : Nat.PartitionVector N :=
  (differencesEquiv N).symm fun i ↦ d i

/-- The reconstructed partition has the prescribed consecutive differences. -/
@[simp]
theorem difference_partitionOfDifferences (d : Fin N →₀ ℕ) (i : Fin N) :
    (partitionOfDifferences d).difference i = d i := by
  rw [← differencesEquiv_apply]
  simp [partitionOfDifferences]

/-- Reconstruction from consecutive differences preserves addition. -/
theorem partitionOfDifferences_add (d e : Fin N →₀ ℕ) :
    partitionOfDifferences (d + e) = partitionOfDifferences d + partitionOfDifferences e := by
  apply (differencesEquiv N).injective
  funext i
  simp [differencesEquiv_apply]

/-- A single nonzero consecutive difference reconstructs a rectangular partition. -/
theorem partitionOfDifferences_single (i : Fin N) (a : ℕ) :
    partitionOfDifferences (Finsupp.single i a) = a • prefixOnes (i + 1) := by
  classical
  apply Nat.PartitionVector.ext
  intro j
  rw [partitionOfDifferences, differencesEquiv_symm_apply]
  simp only [prefixOnes_apply, smul_apply, mul_ite, mul_one, mul_zero]
  by_cases hji : j ≤ i
  · rw [Finset.sum_eq_single i]
    · simp [hji]
    · intro b hb hbi
      simp [hbi]
    · simp [hji]
  · rw [Finset.sum_eq_zero]
    · simp [hji]
    · intro b hb
      have hbi : b ≠ i := by
        intro hbi
        exact hji (hbi ▸ (Finset.mem_Ici.mp hb))
      simp [hbi]

/-- Zero consecutive differences reconstruct the zero partition. -/
@[simp]
theorem partitionOfDifferences_zero :
    partitionOfDifferences (0 : Fin N →₀ ℕ) = 0 := by
  apply Nat.PartitionVector.ext
  intro i
  rw [partitionOfDifferences, differencesEquiv_symm_apply]
  simp

/-- Repeating the rectangular factorization extracts the corresponding power. -/
theorem basis_addRectangle_n
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (zeta t : F) (hzeta : zeta ^ k = 1) (hPieri : SatisfiesPieri P zeta t)
    (hzero : P 0 = 1)
    (hrectangle : SatisfiesRectangles P k)
    (lam : Nat.PartitionVector N) {h : ℕ} (hh : 1 ≤ h) (hhN : h ≤ N) (a : ℕ) :
    P (lam + k • (a • prefixOnes h)) = symmetricExpandedEsymm k h ^ a * P lam := by
  induction a with
  | zero =>
      have hindex : lam + k • (0 • prefixOnes h) = lam := by
        apply Nat.PartitionVector.ext
        intro i
        simp
      rw [hindex, pow_zero, one_mul]
  | succ a ih =>
      have hindex :
          lam + k • (Nat.succ a • prefixOnes h) =
            addRectangle (lam + k • (a • prefixOnes h)) k h := by
        apply Nat.PartitionVector.ext
        intro i
        simp only [add_apply, smul_apply, addRectangle_apply, prefixOnes_apply]
        by_cases hi : i.val < h <;> simp [hi]
        lia
      rw [hindex, basis_addRectangle P zeta t hzeta hPieri hzero hrectangle _ hh hhN, ih,
        pow_succ']
      ac_rfl

/-- Factorization indexed by an arbitrary finitely supported difference vector. -/
theorem basis_add_partitionOfDifferences
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (zeta t : F) (hzeta : zeta ^ k = 1) (hPieri : SatisfiesPieri P zeta t)
    (hzero : P 0 = 1)
    (hrectangle : SatisfiesRectangles P k)
    (tau : Nat.PartitionVector N) (d : Fin N →₀ ℕ) :
    P (tau + k • partitionOfDifferences d) =
      d.prod (fun i a ↦ symmetricExpandedEsymm k (i + 1) ^ a) * P tau := by
  induction d using Finsupp.induction with
  | zero =>
      have hindex : tau + k • partitionOfDifferences 0 = tau := by
        apply Nat.PartitionVector.ext
        intro i
        simp
      rw [hindex]
      simp
  | single_add i a d hi ha ih =>
      have hindex :
          tau + k • partitionOfDifferences (Finsupp.single i a + d) =
            (tau + k • partitionOfDifferences d) + k • (a • prefixOnes (i + 1)) := by
        rw [partitionOfDifferences_add, partitionOfDifferences_single]
        apply Nat.PartitionVector.ext
        intro j
        simp only [Nat.PartitionVector.add_apply, Nat.PartitionVector.smul_apply]
        rw [add_assoc]
        congr 1
        rw [Nat.mul_add]
        exact Nat.add_comm _ _
      have hsingle :
          (Finsupp.single i a).prod
              (fun j b ↦ symmetricExpandedEsymm (F := F) (N := N) k (j + 1) ^ b) =
            symmetricExpandedEsymm (F := F) (N := N) k (i + 1) ^ a := by
        exact Finsupp.prod_single_index (pow_zero _)
      rw [hindex,
        basis_addRectangle_n P zeta t hzeta hPieri hzero hrectangle _ (by simp) (by simp) a,
        ih, Finsupp.prod_add_index']
      · rw [hsingle]
        ac_rfl
      · intro j
        exact pow_zero _
      · intro j b c
        exact pow_add _ _ _

/-- The finitely supported vector of consecutive differences of a partition. -/
def differenceFinsupp (xi : Nat.PartitionVector N) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ xi.difference i

/-- Evaluation of the finitely supported difference vector. -/
@[simp]
theorem differenceFinsupp_apply (xi : Nat.PartitionVector N) (i : Fin N) :
    differenceFinsupp xi i = xi.difference i := rfl

/-- Reconstructing a partition from its difference vector returns the partition. -/
@[simp]
theorem partitionOfDifferences_differenceFinsupp (xi : Nat.PartitionVector N) :
    partitionOfDifferences (differenceFinsupp xi) = xi := by
  apply (differencesEquiv N).injective
  funext i
  simp [differencesEquiv_apply]

/-- A basis vector indexed by `tau + k • xi` factors according to the consecutive differences
of `xi`. -/
theorem basis_add_smul
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (zeta t : F) (hzeta : zeta ^ k = 1) (hPieri : SatisfiesPieri P zeta t)
    (hzero : P 0 = 1)
    (hrectangle : SatisfiesRectangles P k)
    (tau xi : Nat.PartitionVector N) :
    P (tau + k • xi) =
      (∏ i : Fin N, symmetricExpandedEsymm k (i + 1) ^ xi.difference i) * P tau := by
  calc
    P (tau + k • xi) =
        P (tau + k • partitionOfDifferences (differenceFinsupp xi)) := by simp
    _ = (differenceFinsupp xi).prod
          (fun i a ↦ symmetricExpandedEsymm k (i + 1) ^ a) * P tau :=
      basis_add_partitionOfDifferences P zeta t hzeta hPieri hzero hrectangle _ _
    _ = (∏ i : Fin N, symmetricExpandedEsymm k (i + 1) ^ xi.difference i) * P tau := by
      rw [Finsupp.prod_fintype]
      · simp
      · intro i
        exact pow_zero _

/-- Factorization along the restricted/quotient decomposition of a partition vector. -/
theorem basis_decomposition
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (zeta t : F) (hk : 0 < k) (hzeta : zeta ^ k = 1)
    (hPieri : SatisfiesPieri P zeta t) (hzero : P 0 = 1)
    (hrectangle : SatisfiesRectangles P k)
    (lam : Nat.PartitionVector N) :
    P lam =
      (∏ i : Fin N, symmetricExpandedEsymm k (i + 1) ^
        (decompositionEquiv N k hk lam).2.difference i) *
          P (decompositionEquiv N k hk lam).1.1 := by
  calc
    P lam = P ((decompositionEquiv N k hk lam).1.1 +
        k • (decompositionEquiv N k hk lam).2) := by
      exact congrArg P (eq_add_smul_decompositionEquiv hk lam)
    _ = _ := basis_add_smul P zeta t hzeta hPieri hzero hrectangle _ _

/-- The coefficient times the monomial whose exponents are the differences of `xi`. -/
def differenceMonomial (c : F) (xi : Nat.PartitionVector N) :
    MvPolynomial (Fin N) F :=
  C c * monomial (differenceFinsupp xi) 1

/-- Evaluating a difference monomial at expanded elementary symmetric polynomials gives the
factor appearing in the basis factorization. -/
theorem aeval_differenceMonomial (c : F) (xi : Nat.PartitionVector N) :
    aeval (fun i : Fin N ↦ expandedEsymm (F := F) (N := N) k (i + 1))
        (differenceMonomial c xi) =
      C c * ∏ i : Fin N,
        expandedEsymm (F := F) (N := N) k (i + 1) ^ xi.difference i := by
  classical
  rw [differenceMonomial, map_mul, aeval_C, aeval_monomial, Finsupp.prod_fintype]
  · simp
  · intro i
    exact pow_zero _

/-- The polynomial transition coefficient from a restricted partition `lam` to `tau`. -/
def pieriTransitionPolynomial (hk : 0 < k) (zeta t : F) (r : ℕ)
    (tau lam : KRestricted N k) : MvPolynomial (Fin N) F := by
  classical
  exact ∑ delta : Strip N,
    if IsLegal lam.1 delta ∧ stripWeight delta = r ∧
        (decompositionEquiv N k hk (addStrip lam.1 delta)).1 = tau then
      differenceMonomial (pieriCoefficient zeta t lam.1 delta)
        (decompositionEquiv N k hk (addStrip lam.1 delta)).2
    else 0

/-- The matrix of polynomial transition coefficients for the `r`th Pieri multiplication. -/
def pieriTransitionMatrix (hk : 0 < k) (zeta t : F) (r : ℕ) :
    Matrix (KRestricted N k) (KRestricted N k) (MvPolynomial (Fin N) F) :=
  fun tau lam ↦ pieriTransitionPolynomial hk zeta t r tau lam

/-- The zero restricted partition, available when the restriction modulus is positive. -/
def zeroKRestricted (hk : 0 < k) : KRestricted N k :=
  ⟨0, fun i ↦ by
    simpa [Nat.PartitionVector.difference, Nat.PartitionVector.nextPart] using hk⟩

/-- The polynomial underlying a member of the symmetric basis indexed by a restricted
partition. -/
def restrictedBasisPolynomial
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (tau : KRestricted N k) : MvPolynomial (Fin N) F :=
  P tau.1

/-- The restricted basis polynomial at the zero index is one. -/
theorem restrictedBasisPolynomial_zero
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (hzero : P 0 = 1) (hk : 0 < k) :
    restrictedBasisPolynomial P (zeroKRestricted hk) = 1 := by
  change (P 0).val = 1
  exact congrArg Subtype.val hzero

/-- Polynomial-valued form of factorization along the restricted/quotient decomposition. -/
theorem basis_decomposition_val
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (zeta t : F) (hk : 0 < k) (hzeta : zeta ^ k = 1)
    (hPieri : SatisfiesPieri P zeta t) (hzero : P 0 = 1)
    (hrectangle : SatisfiesRectangles P k)
    (lam : Nat.PartitionVector N) :
    (P lam).val =
      (∏ i : Fin N, expandedEsymm k (i + 1) ^
        (decompositionEquiv N k hk lam).2.difference i) *
          (P (decompositionEquiv N k hk lam).1.1).val := by
  have h := congrArg Subtype.val
    (basis_decomposition P zeta t hk hzeta hPieri hzero hrectangle lam)
  simpa [symmetricExpandedEsymm] using h

/-- A specialized Pieri summand factors through the restricted part of its target index. -/
theorem pieriSummand_factor
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (zeta t : F) (hk : 0 < k) (hzeta : zeta ^ k = 1)
    (hPieri : SatisfiesPieri P zeta t) (hzero : P 0 = 1)
    (hrectangle : SatisfiesRectangles P k)
    (lam : Nat.PartitionVector N) (delta : Strip N) :
    pieriCoefficient zeta t lam delta • (P (addStrip lam delta)).val =
      aeval (fun i : Fin N ↦ expandedEsymm k (i + 1))
          (differenceMonomial (pieriCoefficient zeta t lam delta)
            (decompositionEquiv N k hk (addStrip lam delta)).2) *
        (P (decompositionEquiv N k hk (addStrip lam delta)).1.1).val := by
  rw [aeval_differenceMonomial,
    basis_decomposition_val P zeta t hk hzeta hPieri hzero hrectangle]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  ac_rfl

/-- Evaluation of one transition entry, followed by its target basis polynomial, expands as the
corresponding selected strip sum. -/
theorem aeval_pieriTransitionPolynomial_mul
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (hk : 0 < k) (zeta t : F) (r : ℕ) (tau lam : KRestricted N k) :
    aeval (fun i : Fin N ↦ expandedEsymm (F := F) k (i + 1))
        (pieriTransitionPolynomial hk zeta t r tau lam) *
      restrictedBasisPolynomial P tau =
        ∑ delta : Strip N,
          if IsLegal lam.1 delta ∧ stripWeight delta = r ∧
              (decompositionEquiv N k hk (addStrip lam.1 delta)).1 = tau then
            aeval (fun i : Fin N ↦ expandedEsymm k (i + 1))
                (differenceMonomial (pieriCoefficient zeta t lam.1 delta)
                  (decompositionEquiv N k hk (addStrip lam.1 delta)).2) *
              restrictedBasisPolynomial P tau
          else 0 := by
  classical
  rw [pieriTransitionPolynomial, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro delta _
  by_cases hdelta : IsLegal lam.1 delta ∧ stripWeight delta = r ∧
      (decompositionEquiv N k hk (addStrip lam.1 delta)).1 = tau
  · simp [hdelta]
  · simp [hdelta]

/-- The transition matrix satisfies exactly the multiplication identity required by the trace
theorem. -/
theorem pieriTransitionMatrix_mul
    (P : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F))
    (zeta t : F) (hk : 0 < k) (hzeta : zeta ^ k = 1)
    (hPieri : SatisfiesPieri P zeta t) (hzero : P 0 = 1)
    (hrectangle : SatisfiesRectangles P k)
    (r : ℕ) (lam : KRestricted N k) :
    esymm (Fin N) F r * restrictedBasisPolynomial P lam =
      ∑ tau, aeval (fun i : Fin N ↦ expand k (esymm (Fin N) F (i + 1)))
          (pieriTransitionMatrix hk zeta t r tau lam) *
        restrictedBasisPolynomial P tau := by
  classical
  have hpieri := congrArg Subtype.val (hPieri r lam.1)
  have hpieriVal :
      esymm (Fin N) F r * restrictedBasisPolynomial P lam =
        ∑ delta : Strip N,
          if IsLegal lam.1 delta ∧ stripWeight delta = r then
            pieriCoefficient zeta t lam.1 delta • (P (addStrip lam.1 delta)).val
          else 0 := by
    calc
      esymm (Fin N) F r * restrictedBasisPolynomial P lam =
          (symmetricEsymm r * P lam.1).val := rfl
      _ = (∑ delta : Strip N,
          if IsLegal lam.1 delta ∧ stripWeight delta = r then
            pieriCoefficient zeta t lam.1 delta • P (addStrip lam.1 delta)
          else 0).val := hpieri
      _ = _ := by
        rw [AddSubmonoidClass.coe_finsetSum]
        apply Finset.sum_congr rfl
        intro delta _
        by_cases hdelta : IsLegal lam.1 delta ∧ stripWeight delta = r
        · simp [hdelta]
        · simp [hdelta]
  rw [hpieriVal]
  change
    (∑ delta : Strip N,
      if IsLegal lam.1 delta ∧ stripWeight delta = r then
        pieriCoefficient zeta t lam.1 delta • (P (addStrip lam.1 delta)).val
      else 0) =
    ∑ tau, aeval (fun i : Fin N ↦ expandedEsymm k (i + 1))
        (pieriTransitionPolynomial hk zeta t r tau lam) *
      restrictedBasisPolynomial P tau
  simp_rw [aeval_pieriTransitionPolynomial_mul P hk zeta t r]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro delta _
  by_cases hdelta : IsLegal lam.1 delta ∧ stripWeight delta = r
  · simp only [hdelta, and_self, ↓reduceIte]
    rw [pieriSummand_factor P zeta t hk hzeta hPieri hzero hrectangle]
    let tau : KRestricted N k :=
      (decompositionEquiv N k hk (addStrip lam.1 delta)).1
    symm
    rw [Finset.sum_eq_single tau]
    · simp [tau, restrictedBasisPolynomial]
    · intro sigma _ hsigma
      have hne : (decompositionEquiv N k hk (addStrip lam.1 delta)).1 ≠ sigma := by
        intro heq
        apply hsigma
        simpa [tau] using heq.symm
      simp [hne]
    · simp
  · simp only [hdelta, ↓reduceIte]
    symm
    apply Finset.sum_eq_zero
    intro sigma _
    have hn : ¬(IsLegal lam.1 delta ∧ stripWeight delta = r ∧
        (decompositionEquiv N k hk (addStrip lam.1 delta)).1 = sigma) := by
      intro hsigma
      exact hdelta ⟨hsigma.1, hsigma.2.1⟩
    simp [hn]

end PartitionDivision
