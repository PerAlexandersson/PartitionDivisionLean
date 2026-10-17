/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import PartitionDivision.Mathlib.RingTheory.MvPolynomial.Symmetric.Monomial
public import PartitionDivision.Mathlib.RingTheory.MvPolynomial.Antisymmetric

/-!
# Macdonald difference operators

This file constructs the family of Macdonald difference operators on symmetric multivariate
polynomials.  Their numerators are defined without division, and each operator is the unique
symmetric quotient by the Vandermonde polynomial.  The original first operator is retained and
identified with the member `r = 1` of the family.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace MvPolynomial

variable {N : ℕ} {K : Type*}

/-- Multiplication by a homogeneous polynomial shifts a homogeneous component by its degree. -/
theorem homogeneousComponent_mul_of_left_isHomogeneous [CommSemiring K]
    {p g : MvPolynomial (Fin N) K} {a : ℕ} (hp : p.IsHomogeneous a)
    (k : ℕ) (hk : k ≤ g.totalDegree) :
    homogeneousComponent (a + k) (p * g) = p * homogeneousComponent k g := by
  conv_lhs =>
    rw [← g.sum_homogeneousComponent]
  rw [Finset.mul_sum, map_sum]
  simp_rw [homogeneousComponent_of_mem
    (hp.mul (homogeneousComponent_isHomogeneous _ _))]
  simp [Nat.lt_succ_iff.mpr hk]

/-- A nonzero homogeneous factor can be cancelled from a homogeneous product over a domain. -/
theorem IsHomogeneous.of_mul_left [CommRing K] [IsDomain K]
    {p g : MvPolynomial (Fin N) K} {a b : ℕ}
    (hp : p.IsHomogeneous a) (hp0 : p ≠ 0) (hpg : (p * g).IsHomogeneous (a + b)) :
    g.IsHomogeneous b := by
  intro d hd
  let k := d.degree
  have hcomponent : homogeneousComponent k g ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun f : MvPolynomial (Fin N) K ↦ f.coeff d) hzero
    rw [coeff_homogeneousComponent] at hcoeff
    split at hcoeff
    · exact hd hcoeff
    · rename_i hne
      exact (hne rfl).elim
  have hk : k ≤ g.totalDegree := by
    exact le_totalDegree (mem_support_iff.mpr hd)
  have hproduct : p * homogeneousComponent k g ≠ 0 := mul_ne_zero hp0 hcomponent
  have hdegree : a + k = a + b := by
    by_contra hne
    have hzero : homogeneousComponent (a + k) (p * g) = 0 := by
      rw [homogeneousComponent_of_mem hpg]
      split
      · rename_i h
        exact (hne h).elim
      · rfl
    rw [homogeneousComponent_mul_of_left_isHomogeneous hp k hk] at hzero
    exact hproduct hzero
  have hk_eq : k = b := Nat.add_left_cancel hdegree
  have hdeg : d.degree = b := by simpa [k] using hk_eq
  rw [Finsupp.degree_eq_weight_one] at hdeg
  exact hdeg

/-- The Vandermonde polynomial is homogeneous of degree `N.choose 2`. -/
theorem isHomogeneous_vandermonde [CommRing K] :
    (vandermonde N K).IsHomogeneous (N.choose 2) := by
  have hfactor (i j : Fin N) :
      (X i - X j : MvPolynomial (Fin N) K).IsHomogeneous 1 :=
    (isHomogeneous_X K i).sub (isHomogeneous_X K j)
  have hinner (i : Fin N) :
      (∏ j ∈ Finset.Ioi i, (X i - X j : MvPolynomial (Fin N) K)).IsHomogeneous
        (Finset.Ioi i).card := by
    simpa using IsHomogeneous.prod (Finset.Ioi i)
      (fun j ↦ X i - X j) (fun _ ↦ 1) (fun j _ ↦ hfactor i j)
  have hsum : (∑ i : Fin N, (Finset.Ioi i).card) = N.choose 2 := by
    calc
      (∑ i : Fin N, (Finset.Ioi i).card) = ∑ i : Fin N, (Fin.rev i).val := by
        apply Finset.sum_congr rfl
        intro i _
        simp [Fin.card_Ioi, Nat.sub_sub, Nat.add_comm]
      _ = ∑ i : Fin N, i.val := Equiv.sum_comp Fin.revPerm (fun i : Fin N ↦ i.val)
      _ = ∑ i ∈ Finset.range N, i :=
        (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i)) N
      _ = N.choose 2 := by
        rw [Finset.sum_range_id, Nat.choose_two_right]
  rw [vandermonde, ← hsum]
  exact IsHomogeneous.prod Finset.univ
    (fun i ↦ ∏ j ∈ Finset.Ioi i, (X i - X j : MvPolynomial (Fin N) K))
    (fun i ↦ (Finset.Ioi i).card) (fun i _ ↦ hinner i)

/-- Substitute `c * X i` for `X i`, leaving all other variables fixed. -/
def scaleVar [CommSemiring K] (c : K) (i : Fin N) :
    MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K :=
  aeval fun j ↦ if j = i then c • X j else X j

@[simp]
theorem scaleVar_X_same [CommSemiring K] (c : K) (i : Fin N) :
    scaleVar c i (X i) = c • X i := by
  simp [scaleVar]

@[simp]
theorem scaleVar_X_of_ne [CommSemiring K] (c : K) {i j : Fin N} (hji : j ≠ i) :
    scaleVar c i (X j) = X j := by
  simp [scaleVar, hji]

/-- The action of variable scaling on a monomial, expressed as the substituted finite product. -/
theorem scaleVar_monomial [CommSemiring K] (c : K) (i : Fin N)
    (d : Fin N →₀ ℕ) (a : K) :
    scaleVar c i (monomial d a) =
      algebraMap K _ a *
        d.prod (fun j k ↦ (if j = i then c • X j else X j) ^ k) := by
  change (aeval fun j ↦ if j = i then c • X j else X j) (monomial d a) = _
  exact aeval_monomial (fun j ↦ if j = i then c • X j else X j) d a

/-- Scaling commutes with a permutation of variables, with the scaled index permuted as well. -/
theorem rename_scaleVar [CommSemiring K] (e : Equiv.Perm (Fin N))
    (c : K) (i : Fin N) (f : MvPolynomial (Fin N) K) :
    rename e (scaleVar c i f) = scaleVar c (e i) (rename e f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f j hf =>
      by_cases hji : j = i
      · subst j
        simp [hf]
      · have hej : e j ≠ e i := e.injective.ne hji
        simp [hf, hji, hej]

/-- Scaling a variable preserves the homogeneous degree. -/
theorem IsHomogeneous.scaleVar [CommSemiring K] {f : MvPolynomial (Fin N) K}
    {d : ℕ} (hf : f.IsHomogeneous d) (c : K) (i : Fin N) :
    (scaleVar c i f).IsHomogeneous d := by
  change (MvPolynomial.aeval (fun j ↦ if j = i then c • X j else X j) f).IsHomogeneous d
  have h := hf.aeval
    (fun j ↦ if j = i then c • X j else X j)
    (fun j ↦ by
      split_ifs
      · exact (homogeneousSubmodule (Fin N) K 1).smul_mem c (isHomogeneous_X K j)
      · exact isHomogeneous_X K j)
  rw [one_mul] at h
  exact h

/-- Simultaneously substitute `c * X i` for every variable indexed by `I`. -/
def scaleVars [CommSemiring K] (c : K) (I : Finset (Fin N)) :
    MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K :=
  aeval fun j ↦ if j ∈ I then c • X j else X j

@[simp]
theorem scaleVars_X_of_mem [CommSemiring K] (c : K) (I : Finset (Fin N))
    {i : Fin N} (hi : i ∈ I) : scaleVars c I (X i) = c • X i := by
  simp [scaleVars, hi]

@[simp]
theorem scaleVars_X_of_notMem [CommSemiring K] (c : K) (I : Finset (Fin N))
    {i : Fin N} (hi : i ∉ I) : scaleVars c I (X i) = X i := by
  simp [scaleVars, hi]

/-- Simultaneous scaling on a singleton is scaling of that single variable. -/
theorem scaleVars_singleton [CommSemiring K] (c : K) (i : Fin N) :
    scaleVars c {i} = scaleVar c i := by
  apply MvPolynomial.algHom_ext
  intro j
  by_cases hji : j = i
  · subst j
    simp [scaleVars]
  · simp [scaleVars, hji]

/-- Simultaneous scaling commutes with a permutation of variables. -/
theorem rename_scaleVars [CommSemiring K] (e : Equiv.Perm (Fin N))
    (c : K) (I : Finset (Fin N)) (f : MvPolynomial (Fin N) K) :
    rename e (scaleVars c I f) = scaleVars c (I.map e.toEmbedding) (rename e f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f j hf =>
      by_cases hj : j ∈ I
      · simp [hf, hj]
      · simp [hf, hj]

/-- Simultaneous variable scaling preserves homogeneous degree. -/
theorem IsHomogeneous.scaleVars [CommSemiring K] {f : MvPolynomial (Fin N) K}
    {d : ℕ} (hf : f.IsHomogeneous d) (c : K) (I : Finset (Fin N)) :
    (scaleVars c I f).IsHomogeneous d := by
  change (MvPolynomial.aeval
    (fun j ↦ if j ∈ I then c • X j else X j) f).IsHomogeneous d
  have h := hf.aeval
    (fun j ↦ if j ∈ I then c • X j else X j)
    (fun j ↦ by
      split_ifs
      · exact (homogeneousSubmodule (Fin N) K 1).smul_mem c (isHomogeneous_X K j)
      · exact isHomogeneous_X K j)
  rw [one_mul] at h
  exact h

/-- The numerator in the first Macdonald difference operator. -/
def macdonaldNumerator [CommRing K] (q t : K) (f : MvPolynomial (Fin N) K) :
    MvPolynomial (Fin N) K :=
  ∑ i, scaleVar t i (vandermonde N K) * scaleVar q i f

@[simp]
theorem macdonaldNumerator_zero [CommRing K] (q t : K) :
    macdonaldNumerator q t (0 : MvPolynomial (Fin N) K) = 0 := by
  simp [macdonaldNumerator]

/-- The numerator is additive in its polynomial argument. -/
theorem macdonaldNumerator_add [CommRing K] (q t : K)
    (f g : MvPolynomial (Fin N) K) :
    macdonaldNumerator q t (f + g) =
      macdonaldNumerator q t f + macdonaldNumerator q t g := by
  simp only [macdonaldNumerator, map_add, mul_add, Finset.sum_add_distrib]

/-- The numerator is linear in its polynomial argument. -/
theorem macdonaldNumerator_smul [CommRing K] (q t c : K)
    (f : MvPolynomial (Fin N) K) :
    macdonaldNumerator q t (c • f) = c • macdonaldNumerator q t f := by
  simp only [macdonaldNumerator, map_smul, mul_smul_comm, Finset.smul_sum]

/-- The numerator is antisymmetric whenever its polynomial argument is symmetric. -/
theorem isAntisymmetric_macdonaldNumerator [CommRing K]
    (q t : K) {f : MvPolynomial (Fin N) K} (hf : f.IsSymmetric) :
    (macdonaldNumerator q t f).IsAntisymmetric := by
  intro e
  simp only [macdonaldNumerator, map_sum, map_mul, rename_scaleVar,
    isAntisymmetric_vandermonde N K e, hf e]
  calc
    ∑ x, scaleVar t (e x) ((e.sign : ℤ) • vandermonde N K) *
        scaleVar q (e x) f =
        ∑ i, scaleVar t i ((e.sign : ℤ) • vandermonde N K) *
          scaleVar q i f := by
      simpa only using e.bijective.sum_comp
        (fun i : Fin N ↦ scaleVar t i ((e.sign : ℤ) • vandermonde N K) *
          scaleVar q i f)
    _ = (e.sign : ℤ) • ∑ i, scaleVar t i (vandermonde N K) *
        scaleVar q i f := by
      simp_rw [map_zsmul, smul_mul_assoc]
      exact Finset.smul_sum.symm

/-- If the Vandermonde is supplied with its homogeneous degree, then the numerator shifts the
degree of a homogeneous input by that degree. -/
theorem IsHomogeneous.macdonaldNumerator [CommRing K] (q t : K)
    {f : MvPolynomial (Fin N) K} {d v : ℕ}
    (hv : (vandermonde N K).IsHomogeneous v) (hf : f.IsHomogeneous d) :
    (macdonaldNumerator q t f).IsHomogeneous (v + d) := by
  apply IsHomogeneous.sum
  intro i _
  exact (hv.scaleVar t i).mul (hf.scaleVar q i)

/-- The numerator has a symmetric quotient by the Vandermonde. -/
theorem exists_macdonaldDPolynomial [Field K] [CharZero K] (q t : K)
    (f : symmetricSubalgebra (Fin N) K) :
    ∃ g : MvPolynomial (Fin N) K,
      g.IsSymmetric ∧ macdonaldNumerator q t f = vandermonde N K * g :=
  exists_isSymmetric_mul_eq_of_isAntisymmetric
    (isAntisymmetric_macdonaldNumerator q t f.property)

/-- A chosen symmetric quotient of the Macdonald numerator by the Vandermonde. -/
def macdonaldDPolynomial [Field K] [CharZero K] (q t : K)
    (f : symmetricSubalgebra (Fin N) K) : MvPolynomial (Fin N) K :=
  Classical.choose (exists_macdonaldDPolynomial q t f)

/-- The chosen quotient defining the Macdonald operator is symmetric. -/
theorem macdonaldDPolynomial_isSymmetric [Field K] [CharZero K] (q t : K)
    (f : symmetricSubalgebra (Fin N) K) : (macdonaldDPolynomial q t f).IsSymmetric :=
  (Classical.choose_spec (exists_macdonaldDPolynomial q t f)).1

/-- The chosen quotient satisfies the numerator equation. -/
theorem macdonaldDPolynomial_spec [Field K] [CharZero K] (q t : K)
    (f : symmetricSubalgebra (Fin N) K) :
    macdonaldNumerator q t f = vandermonde N K * macdonaldDPolynomial q t f :=
  (Classical.choose_spec (exists_macdonaldDPolynomial q t f)).2

/-- Multiplication by the Vandermonde is injective over a field. -/
theorem vandermonde_mul_injective [Field K] :
    Function.Injective (fun g : MvPolynomial (Fin N) K ↦ vandermonde N K * g) := by
  intro f g h
  exact mul_left_cancel₀ (vandermonde_ne_zero N K) h

/-- The chosen quotient is additive. -/
theorem macdonaldDPolynomial_add [Field K] [CharZero K] (q t : K)
    (f g : symmetricSubalgebra (Fin N) K) :
    macdonaldDPolynomial q t (f + g) =
      macdonaldDPolynomial q t f + macdonaldDPolynomial q t g := by
  apply vandermonde_mul_injective
  calc
    vandermonde N K * macdonaldDPolynomial q t (f + g) =
        macdonaldNumerator q t (f + g) := (macdonaldDPolynomial_spec q t (f + g)).symm
    _ = macdonaldNumerator q t f + macdonaldNumerator q t g := by
      change macdonaldNumerator q t
        ((f : MvPolynomial (Fin N) K) + (g : MvPolynomial (Fin N) K)) = _
      exact macdonaldNumerator_add q t
        (f : MvPolynomial (Fin N) K) (g : MvPolynomial (Fin N) K)
    _ = vandermonde N K *
        (macdonaldDPolynomial q t f + macdonaldDPolynomial q t g) := by
      rw [mul_add, ← macdonaldDPolynomial_spec, ← macdonaldDPolynomial_spec]

/-- The chosen quotient respects scalar multiplication. -/
theorem macdonaldDPolynomial_smul [Field K] [CharZero K] (q t c : K)
    (f : symmetricSubalgebra (Fin N) K) :
    macdonaldDPolynomial q t (c • f) = c • macdonaldDPolynomial q t f := by
  apply vandermonde_mul_injective
  calc
    vandermonde N K * macdonaldDPolynomial q t (c • f) =
        macdonaldNumerator q t (c • f) :=
      (macdonaldDPolynomial_spec q t (c • f)).symm
    _ = c • macdonaldNumerator q t f := by
      change macdonaldNumerator q t (c • (f : MvPolynomial (Fin N) K)) = _
      exact macdonaldNumerator_smul q t c (f : MvPolynomial (Fin N) K)
    _ = c • (vandermonde N K * macdonaldDPolynomial q t f) := by
      rw [← macdonaldDPolynomial_spec]
    _ = vandermonde N K * (c • macdonaldDPolynomial q t f) := by
      exact (mul_smul_comm c (vandermonde N K) (macdonaldDPolynomial q t f)).symm

/-- The first Macdonald difference operator on symmetric polynomials. -/
def macdonaldD [Field K] [CharZero K] (q t : K) :
    symmetricSubalgebra (Fin N) K →ₗ[K] symmetricSubalgebra (Fin N) K where
  toFun f := ⟨macdonaldDPolynomial q t f, macdonaldDPolynomial_isSymmetric q t f⟩
  map_add' f g := Subtype.ext (macdonaldDPolynomial_add q t f g)
  map_smul' c f := Subtype.ext (macdonaldDPolynomial_smul q t c f)

/-- The defining equation for the first Macdonald difference operator. -/
theorem vandermonde_mul_macdonaldD [Field K] [CharZero K] (q t : K)
    (f : symmetricSubalgebra (Fin N) K) :
    vandermonde N K * (macdonaldD q t f : MvPolynomial (Fin N) K) =
      macdonaldNumerator q t f := by
  rw [macdonaldD]
  exact (macdonaldDPolynomial_spec q t f).symm

/-- The numerator of the `r`-th Macdonald difference operator. -/
def macdonaldOpNumerator [CommRing K] (q t : K) (r : ℕ)
    (f : MvPolynomial (Fin N) K) : MvPolynomial (Fin N) K :=
  ∑ I ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
    scaleVars t I (vandermonde N K) * scaleVars q I f

@[simp]
theorem macdonaldOpNumerator_zero [CommRing K] (q t : K) (r : ℕ) :
    macdonaldOpNumerator q t r (0 : MvPolynomial (Fin N) K) = 0 := by
  simp [macdonaldOpNumerator]

/-- The `r`-th numerator is additive in its polynomial argument. -/
theorem macdonaldOpNumerator_add [CommRing K] (q t : K) (r : ℕ)
    (f g : MvPolynomial (Fin N) K) :
    macdonaldOpNumerator q t r (f + g) =
      macdonaldOpNumerator q t r f + macdonaldOpNumerator q t r g := by
  simp only [macdonaldOpNumerator, map_add, mul_add, Finset.sum_add_distrib]

/-- The `r`-th numerator is linear in its polynomial argument. -/
theorem macdonaldOpNumerator_smul [CommRing K] (q t c : K) (r : ℕ)
    (f : MvPolynomial (Fin N) K) :
    macdonaldOpNumerator q t r (c • f) = c • macdonaldOpNumerator q t r f := by
  simp only [macdonaldOpNumerator, map_smul, mul_smul_comm, Finset.smul_sum]

/-- The `r`-th numerator is antisymmetric whenever its argument is symmetric. -/
theorem isAntisymmetric_macdonaldOpNumerator [CommRing K]
    (q t : K) (r : ℕ) {f : MvPolynomial (Fin N) K} (hf : f.IsSymmetric) :
    (macdonaldOpNumerator q t r f).IsAntisymmetric := by
  intro e
  simp only [macdonaldOpNumerator, map_sum, map_mul, rename_scaleVars,
    isAntisymmetric_vandermonde N K e, hf e]
  calc
    ∑ I ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
        scaleVars t (I.map e.toEmbedding) ((e.sign : ℤ) • vandermonde N K) *
          scaleVars q (I.map e.toEmbedding) f =
        ∑ J ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
          scaleVars t J ((e.sign : ℤ) • vandermonde N K) * scaleVars q J f := by
      exact Finset.sum_equiv (Equiv.finsetCongr e)
        (by intro I; simp [Finset.mem_powersetCard]) (by intro I _; rfl)
    _ = (e.sign : ℤ) •
        ∑ I ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
          scaleVars t I (vandermonde N K) * scaleVars q I f := by
      simp_rw [map_zsmul, smul_mul_assoc]
      simp only [Finset.smul_sum]

/-- If the Vandermonde has homogeneous degree `v`, the `r`-th numerator shifts a homogeneous
input degree by `v`. -/
theorem IsHomogeneous.macdonaldOpNumerator [CommRing K] (q t : K) (r : ℕ)
    {f : MvPolynomial (Fin N) K} {d v : ℕ}
    (hv : (vandermonde N K).IsHomogeneous v) (hf : f.IsHomogeneous d) :
    (macdonaldOpNumerator q t r f).IsHomogeneous (v + d) := by
  apply IsHomogeneous.sum
  intro I _
  exact (hv.scaleVars t I).mul (hf.scaleVars q I)

/-- The `r`-th numerator has a symmetric quotient by the Vandermonde. -/
theorem exists_macdonaldOpPolynomial [Field K] [CharZero K] (q t : K) (r : ℕ)
    (f : symmetricSubalgebra (Fin N) K) :
    ∃ g : MvPolynomial (Fin N) K,
      g.IsSymmetric ∧ macdonaldOpNumerator q t r f = vandermonde N K * g :=
  exists_isSymmetric_mul_eq_of_isAntisymmetric
    (isAntisymmetric_macdonaldOpNumerator q t r f.property)

/-- A chosen symmetric quotient defining the `r`-th Macdonald operator. -/
def macdonaldOpPolynomial [Field K] [CharZero K] (q t : K) (r : ℕ)
    (f : symmetricSubalgebra (Fin N) K) : MvPolynomial (Fin N) K :=
  Classical.choose (exists_macdonaldOpPolynomial q t r f)

/-- The chosen quotient for the `r`-th operator is symmetric. -/
theorem macdonaldOpPolynomial_isSymmetric [Field K] [CharZero K]
    (q t : K) (r : ℕ) (f : symmetricSubalgebra (Fin N) K) :
    (macdonaldOpPolynomial q t r f).IsSymmetric :=
  (Classical.choose_spec (exists_macdonaldOpPolynomial q t r f)).1

/-- The chosen quotient for the `r`-th operator satisfies the numerator equation. -/
theorem macdonaldOpPolynomial_spec [Field K] [CharZero K]
    (q t : K) (r : ℕ) (f : symmetricSubalgebra (Fin N) K) :
    macdonaldOpNumerator q t r f = vandermonde N K * macdonaldOpPolynomial q t r f :=
  (Classical.choose_spec (exists_macdonaldOpPolynomial q t r f)).2

/-- The chosen quotient for the `r`-th operator is additive. -/
theorem macdonaldOpPolynomial_add [Field K] [CharZero K]
    (q t : K) (r : ℕ) (f g : symmetricSubalgebra (Fin N) K) :
    macdonaldOpPolynomial q t r (f + g) =
      macdonaldOpPolynomial q t r f + macdonaldOpPolynomial q t r g := by
  apply vandermonde_mul_injective
  calc
    vandermonde N K * macdonaldOpPolynomial q t r (f + g) =
        macdonaldOpNumerator q t r (f + g) :=
      (macdonaldOpPolynomial_spec q t r (f + g)).symm
    _ = macdonaldOpNumerator q t r f + macdonaldOpNumerator q t r g := by
      change macdonaldOpNumerator q t r
        ((f : MvPolynomial (Fin N) K) + (g : MvPolynomial (Fin N) K)) = _
      exact macdonaldOpNumerator_add q t r
        (f : MvPolynomial (Fin N) K) (g : MvPolynomial (Fin N) K)
    _ = vandermonde N K *
        (macdonaldOpPolynomial q t r f + macdonaldOpPolynomial q t r g) := by
      rw [mul_add, ← macdonaldOpPolynomial_spec, ← macdonaldOpPolynomial_spec]

/-- The chosen quotient for the `r`-th operator respects scalar multiplication. -/
theorem macdonaldOpPolynomial_smul [Field K] [CharZero K]
    (q t c : K) (r : ℕ) (f : symmetricSubalgebra (Fin N) K) :
    macdonaldOpPolynomial q t r (c • f) = c • macdonaldOpPolynomial q t r f := by
  apply vandermonde_mul_injective
  calc
    vandermonde N K * macdonaldOpPolynomial q t r (c • f) =
        macdonaldOpNumerator q t r (c • f) :=
      (macdonaldOpPolynomial_spec q t r (c • f)).symm
    _ = c • macdonaldOpNumerator q t r f := by
      change macdonaldOpNumerator q t r (c • (f : MvPolynomial (Fin N) K)) = _
      exact macdonaldOpNumerator_smul q t c r (f : MvPolynomial (Fin N) K)
    _ = c • (vandermonde N K * macdonaldOpPolynomial q t r f) := by
      rw [← macdonaldOpPolynomial_spec]
    _ = vandermonde N K * (c • macdonaldOpPolynomial q t r f) := by
      exact (mul_smul_comm c (vandermonde N K)
        (macdonaldOpPolynomial q t r f)).symm

/-- The `r`-th Macdonald difference operator on symmetric polynomials. -/
def macdonaldOp [Field K] [CharZero K] (q t : K) (r : ℕ) :
    symmetricSubalgebra (Fin N) K →ₗ[K] symmetricSubalgebra (Fin N) K where
  toFun f := ⟨macdonaldOpPolynomial q t r f,
    macdonaldOpPolynomial_isSymmetric q t r f⟩
  map_add' f g := Subtype.ext (macdonaldOpPolynomial_add q t r f g)
  map_smul' c f := Subtype.ext (macdonaldOpPolynomial_smul q t c r f)

/-- The defining equation for the `r`-th Macdonald difference operator. -/
theorem vandermonde_mul_macdonaldOp [Field K] [CharZero K]
    (q t : K) (r : ℕ) (f : symmetricSubalgebra (Fin N) K) :
    vandermonde N K * (macdonaldOp q t r f : MvPolynomial (Fin N) K) =
      macdonaldOpNumerator q t r f := by
  rw [macdonaldOp]
  exact (macdonaldOpPolynomial_spec q t r f).symm

/-- Every Macdonald operator in the family preserves homogeneous degree. -/
theorem IsHomogeneous.macdonaldOp [Field K] [CharZero K]
    (q t : K) (r : ℕ) {d : ℕ} {f : symmetricSubalgebra (Fin N) K}
    (hf : (f : MvPolynomial (Fin N) K).IsHomogeneous d) :
    ((macdonaldOp q t r f : symmetricSubalgebra (Fin N) K) :
      MvPolynomial (Fin N) K).IsHomogeneous d := by
  apply isHomogeneous_vandermonde.of_mul_left (vandermonde_ne_zero N K)
  rw [vandermonde_mul_macdonaldOp]
  exact isHomogeneous_vandermonde.macdonaldOpNumerator q t r hf

/-- The numerator for `r = 1` agrees with the original first-operator numerator. -/
theorem macdonaldOpNumerator_one [CommRing K] (q t : K)
    (f : MvPolynomial (Fin N) K) :
    macdonaldOpNumerator q t 1 f = macdonaldNumerator q t f := by
  simp [macdonaldOpNumerator, macdonaldNumerator, Finset.powersetCard_one,
    scaleVars_singleton]

/-- The member `r = 1` of the operator family is the original first operator. -/
theorem macdonaldOp_one [Field K] [CharZero K] (q t : K) :
    macdonaldOp (N := N) q t 1 = macdonaldD q t := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply vandermonde_mul_injective
  change vandermonde N K * (macdonaldOp q t 1 f : MvPolynomial (Fin N) K) =
    vandermonde N K * (macdonaldD q t f : MvPolynomial (Fin N) K)
  rw [vandermonde_mul_macdonaldOp, vandermonde_mul_macdonaldD,
    macdonaldOpNumerator_one]

/-- The original first Macdonald operator preserves homogeneous degree. -/
theorem IsHomogeneous.macdonaldD [Field K] [CharZero K]
    (q t : K) {d : ℕ} {f : symmetricSubalgebra (Fin N) K}
    (hf : (f : MvPolynomial (Fin N) K).IsHomogeneous d) :
    ((macdonaldD q t f : symmetricSubalgebra (Fin N) K) :
      MvPolynomial (Fin N) K).IsHomogeneous d := by
  rw [← macdonaldOp_one q t]
  exact hf.macdonaldOp q t 1

/-- The expected diagonal coefficient of the first Macdonald operator at an exponent vector. -/
def macdonaldEigenvalue [CommSemiring K] (q t : K) (lambda : Fin N → ℕ) : K :=
  ∑ i, q ^ lambda i * t ^ (Fin.rev i).val

/-- The expected diagonal coefficient of the `r`-th Macdonald operator. -/
def macdonaldEigenvalueR [CommSemiring K] (q t : K) (r : ℕ)
    (lambda : Fin N → ℕ) : K :=
  ∑ I ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
    ∏ i ∈ I, q ^ lambda i * t ^ (Fin.rev i).val

/-- The diagonal coefficient for `r = 1` is the original first-operator coefficient. -/
theorem macdonaldEigenvalueR_one [CommSemiring K] (q t : K) (lambda : Fin N → ℕ) :
    macdonaldEigenvalueR q t 1 lambda = macdonaldEigenvalue q t lambda := by
  simp [macdonaldEigenvalueR, macdonaldEigenvalue, Finset.powersetCard_one]

/-- The bivariate polynomial whose specialization is a Macdonald diagonal coefficient. -/
def macdonaldEigenvaluePolynomial (lambda : Fin N → ℕ) :
    MvPolynomial (Fin 2) ℚ :=
  ∑ i, X 0 ^ lambda i * X 1 ^ (Fin.rev i).val

/-- The bivariate exponent attached to one summand of the universal diagonal coefficient. -/
def macdonaldEigenvalueExponent (lambda : Fin N → ℕ) (i : Fin N) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (lambda i) + Finsupp.single 1 (Fin.rev i).val

/-- For a fixed exponent vector, the bivariate exponents in the universal diagonal coefficient
are pairwise distinct. -/
theorem macdonaldEigenvalueExponent_injective (lambda : Fin N → ℕ) :
    Function.Injective (macdonaldEigenvalueExponent lambda) := by
  intro i j hij
  apply Fin.rev_injective
  apply Fin.ext
  have h := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 1) hij
  simpa [macdonaldEigenvalueExponent] using h

/-- The universal diagonal coefficient is the sum of its explicitly indexed monomials. -/
theorem macdonaldEigenvaluePolynomial_eq_sum_monomial (lambda : Fin N → ℕ) :
    macdonaldEigenvaluePolynomial lambda =
      ∑ i, monomial (macdonaldEigenvalueExponent lambda i) 1 := by
  apply Finset.sum_congr rfl
  intro i _
  simp [macdonaldEigenvalueExponent,
    X_pow_eq_monomial, monomial_mul_monomial]

/-- Each explicitly indexed monomial has coefficient one in the universal diagonal
coefficient. -/
theorem coeff_macdonaldEigenvaluePolynomial (lambda : Fin N → ℕ) (i : Fin N) :
    (macdonaldEigenvaluePolynomial lambda).coeff
      (macdonaldEigenvalueExponent lambda i) = 1 := by
  rw [macdonaldEigenvaluePolynomial_eq_sum_monomial, coeff_sum]
  classical
  simp [coeff_monomial, (macdonaldEigenvalueExponent_injective lambda).eq_iff]

/-- An algebra map taking the two variables to `q` and `t` specializes the universal diagonal
coefficient polynomial to the corresponding Macdonald diagonal coefficient. -/
theorem map_macdonaldEigenvaluePolynomial [Field K] [CharZero K] [Algebra ℚ K]
    (q t : K) (phi : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] K)
    (hq : phi (X (0 : Fin 2)) = q) (ht : phi (X (1 : Fin 2)) = t)
    (lambda : Fin N → ℕ) :
    phi (macdonaldEigenvaluePolynomial lambda) = macdonaldEigenvalue q t lambda := by
  simp [macdonaldEigenvaluePolynomial, macdonaldEigenvalue, hq, ht]

/-- Algebraic independence of `q` and `t` makes all Macdonald diagonal coefficients distinct,
even without a monotonicity assumption on the exponent vectors. -/
theorem macdonaldEigenvalue_injective [Field K] [CharZero K] [Algebra ℚ K]
    (q t : K) (phi : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] K)
    (hphi : Function.Injective phi)
    (hq : phi (X (0 : Fin 2)) = q) (ht : phi (X (1 : Fin 2)) = t) :
    Function.Injective (macdonaldEigenvalue (N := N) q t) := by
  intro lambda mu heq
  have hpoly : macdonaldEigenvaluePolynomial lambda =
      macdonaldEigenvaluePolynomial mu := by
    apply hphi
    rw [map_macdonaldEigenvaluePolynomial q t phi hq ht,
      map_macdonaldEigenvaluePolynomial q t phi hq ht, heq]
  funext i
  have hc : (macdonaldEigenvaluePolynomial mu).coeff
      (macdonaldEigenvalueExponent lambda i) = 1 := by
    rw [← hpoly]
    exact coeff_macdonaldEigenvaluePolynomial lambda i
  have hex : ∃ j, macdonaldEigenvalueExponent mu j =
      macdonaldEigenvalueExponent lambda i := by
    by_contra hnone
    simp only [not_exists] at hnone
    rw [macdonaldEigenvaluePolynomial_eq_sum_monomial, coeff_sum] at hc
    simp [coeff_monomial, hnone] at hc
  obtain ⟨j, hj⟩ := hex
  have hrev : Fin.rev j = Fin.rev i := by
    apply Fin.ext
    have h := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 1) hj
    simpa [macdonaldEigenvalueExponent] using h
  have hji : j = i := Fin.rev_injective hrev
  subst j
  have h := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 0) hj
  simpa [macdonaldEigenvalueExponent] using h.symm

end MvPolynomial
