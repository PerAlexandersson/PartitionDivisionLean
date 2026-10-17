/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Division.RootOfUnity
public import PartitionDivision.Macdonald.LexUnitriangular
public import PartitionDivision.Macdonald.Operator
public import PartitionDivision.Mathlib.RingTheory.MvPolynomial.Symmetric.MonomialBasis
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Rectangular Macdonald polynomials at a root of unity

This file isolates the operator argument which identifies the Macdonald polynomial indexed by
`k • prefixOnes h` with the expanded elementary symmetric polynomial.  Lexicographic
unitriangularity is kept as an explicit hypothesis, so the result does not depend on a particular
construction of Macdonald polynomials.
-/

@[expose] public section

noncomputable section

open scoped BigOperators MonomialOrder

namespace MvPolynomial

variable {N : ℕ}

/-- Expansion by `k` is fixed by scaling one variable by a `k`-th root of unity. -/
theorem scaleVar_expand_of_pow_eq_one {R : Type*} [CommSemiring R] (zeta : R) (k : ℕ)
    (hzeta : zeta ^ k = 1) (i : Fin N) (f : MvPolynomial (Fin N) R) :
    scaleVar zeta i (expand k f) = expand k f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f j hf =>
      by_cases hji : j = i
      · subst j
        simp only [map_mul, expand_X, map_pow, scaleVar_X_same, hf]
        rw [smul_pow, hzeta, one_smul]
      · simp [hf, hji]

private theorem coeff_prod_of_degree_le {K ι : Type*} [CommRing K]
    (m : MonomialOrder (Fin N)) (P : ι → MvPolynomial (Fin N) K)
    (d : ι → (Fin N →₀ ℕ)) (s : Finset ι)
    (hdegree : ∀ i ∈ s, m.degree (P i) ≼[m] d i) :
    (∏ i ∈ s, P i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (P i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [m.coeff_mul_of_add_of_degree_le (hdegree a (Finset.mem_insert_self a s))]
      · rw [ih (fun i hi ↦ hdegree i (Finset.mem_insert_of_mem hi))]
        rw [Finset.prod_insert ha]
      · apply le_trans m.degree_prod_le
        simpa only [map_sum] using
          (Finset.sum_le_sum fun i hi ↦ hdegree i (Finset.mem_insert_of_mem hi))

private theorem lex_single_lt_single {i j : Fin N} (hij : i < j) :
    Finsupp.single j 1 ≺[MonomialOrder.lex] Finsupp.single i 1 := by
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
  refine ⟨i, ?_, ?_⟩
  · intro d hdi
    have hdj : d ≠ j := ne_of_lt (hdi.trans hij)
    simp [ne_of_lt hdi, hdj]
  · simp [ne_of_lt hij]

private theorem degree_scaleVar_vandermondeFactor_le {K : Type*} [Field K]
    (t : K) (a i j : Fin N) (hij : i < j) :
    MonomialOrder.lex.degree (scaleVar t a (X i - X j))
      ≼[MonomialOrder.lex] Finsupp.single i 1 := by
  by_cases hai : i = a
  · subst a
    rw [map_sub, scaleVar_X_same, scaleVar_X_of_ne t hij.ne']
    apply le_trans MonomialOrder.degree_sub_le
    rw [sup_le_iff]
    constructor
    · apply le_trans MonomialOrder.degree_smul_le
      rw [MonomialOrder.degree_X]
    · rw [MonomialOrder.degree_X]
      exact (lex_single_lt_single hij).le
  · by_cases haj : j = a
    · subst a
      rw [map_sub, scaleVar_X_of_ne t hai, scaleVar_X_same]
      apply le_trans MonomialOrder.degree_sub_le
      rw [sup_le_iff]
      constructor
      · rw [MonomialOrder.degree_X]
      · apply le_trans MonomialOrder.degree_smul_le
        rw [MonomialOrder.degree_X]
        exact (lex_single_lt_single hij).le
    · rw [map_sub, scaleVar_X_of_ne t hai, scaleVar_X_of_ne t haj]
      exact
        (show MonomialOrder.lex.degree (X i - X j : MvPolynomial (Fin N) K)
            ≼[MonomialOrder.lex] Finsupp.single i 1 by
          apply le_trans MonomialOrder.degree_sub_le
          rw [sup_le_iff, MonomialOrder.degree_X, MonomialOrder.degree_X]
          exact ⟨le_rfl, (lex_single_lt_single hij).le⟩)

private theorem coeff_scaleVar_vandermondeFactor {K : Type*} [Field K]
    (t : K) (a i j : Fin N) (hij : i < j) :
    (scaleVar t a (X i - X j)).coeff (Finsupp.single i 1) =
      if i = a then t else 1 := by
  by_cases hai : i = a
  · subst a
    have hji : j ≠ i := hij.ne'
    have hjscale : scaleVar t i (X j) = X j := scaleVar_X_of_ne t hji
    rw [map_sub, scaleVar_X_same, hjscale]
    simp only [AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_smul,
      Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, coeff_single_X,
      and_self, reduceIte, smul_eq_mul, mul_one, true_and, sub_eq_self,
      ite_eq_right_iff, one_ne_zero, imp_false, ne_eq]
    exact hji
  · by_cases haj : j = a
    · subst a
      rw [map_sub, scaleVar_X_of_ne t hai, scaleVar_X_same]
      have hsingle : Finsupp.single j 1 ≠ Finsupp.single i 1 :=
        (Finsupp.single_left_injective one_ne_zero).ne hij.ne'
      simp [coeff_X, hsingle, hai]
    · rw [map_sub, scaleVar_X_of_ne t hai, scaleVar_X_of_ne t haj]
      have hsingle : Finsupp.single j 1 ≠ Finsupp.single i 1 :=
        (Finsupp.single_left_injective one_ne_zero).ne hij.ne'
      simp [coeff_X, hsingle, hai]

private def vandermondeLexExponent (N : ℕ) : Fin N →₀ ℕ :=
  ∑ i, ∑ _j ∈ Finset.Ioi i, Finsupp.single i 1

private theorem coeff_scaleVar_vandermonde {K : Type*} [Field K]
    (t : K) (a : Fin N) :
    (scaleVar t a (vandermonde N K)).coeff (vandermondeLexExponent N) =
      t ^ (Fin.rev a).val := by
  classical
  rw [vandermonde, map_prod]
  simp_rw [map_prod]
  change (∏ x, ∏ x_1 ∈ Finset.Ioi x, scaleVar t a (X x - X x_1)).coeff
    (∑ i, ∑ _j ∈ Finset.Ioi i, Finsupp.single i 1) = _
  rw [coeff_prod_of_degree_le MonomialOrder.lex
    (fun i : Fin N ↦ ∏ j ∈ Finset.Ioi i, scaleVar t a (X i - X j))
    (fun i : Fin N ↦ ∑ _j ∈ Finset.Ioi i, Finsupp.single i 1) Finset.univ]
  · have hinner (i : Fin N) :
        (∏ j ∈ Finset.Ioi i, scaleVar t a (X i - X j)).coeff
            (∑ _j ∈ Finset.Ioi i, Finsupp.single i 1) =
          ∏ _j ∈ Finset.Ioi i, if i = a then t else 1 := by
      rw [coeff_prod_of_degree_le MonomialOrder.lex
        (fun j : Fin N ↦ scaleVar t a (X i - X j))
        (fun _j : Fin N ↦ Finsupp.single i 1)]
      · apply Finset.prod_congr rfl
        intro j hj
        exact coeff_scaleVar_vandermondeFactor t a i j (Finset.mem_Ioi.mp hj)
      · intro j hj
        exact degree_scaleVar_vandermondeFactor_le t a i j (Finset.mem_Ioi.mp hj)
    simp_rw [hinner, Finset.prod_const]
    rw [Finset.prod_eq_single a]
    · simp [Fin.card_Ioi, Nat.sub_sub, Nat.add_comm]
    · intro i _ hia
      simp [hia]
    · simp
  · intro i _
    apply le_trans MonomialOrder.degree_prod_le
    exact Finset.sum_le_sum fun j hj ↦
      degree_scaleVar_vandermondeFactor_le t a i j (Finset.mem_Ioi.mp hj)

private theorem scaleVar_one {K : Type*} [CommSemiring K] (i : Fin N)
    (f : MvPolynomial (Fin N) K) : scaleVar 1 i f = f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f j hf =>
      by_cases hji : j = i
      · subst j
        simp [hf]
      · simp [hf, hji]

private theorem coeff_vandermonde {K : Type*} [Field K] :
    (vandermonde N K).coeff (vandermondeLexExponent N) = 1 := by
  cases N with
  | zero => simp [vandermonde, vandermondeLexExponent]
  | succ N =>
      let a : Fin (N + 1) := 0
      have h := coeff_scaleVar_vandermonde (N := N + 1) (K := K) (1 : K) a
      rw [scaleVar_one] at h
      simpa using h

/-- The sum of all single-variable scalings of the Vandermonde is its `t`-integer multiple. -/
theorem sum_scaleVar_vandermonde [Field K] [CharZero K] (t : K) :
    ∑ i : Fin N, scaleVar t i (vandermonde N K) =
      (∑ i : Fin N, t ^ (Fin.rev i).val) • vandermonde N K := by
  let p := ∑ i : Fin N, scaleVar t i (vandermonde N K)
  have hpanti : p.IsAntisymmetric := by
    simpa [p, macdonaldNumerator] using
      (isAntisymmetric_macdonaldNumerator (N := N) (1 : K) t
        (esymm_isSymmetric (Fin N) K 0))
  obtain ⟨g, hg, hpg⟩ := exists_isSymmetric_mul_eq_of_isAntisymmetric hpanti
  have hphom : p.IsHomogeneous (N.choose 2) := by
    apply IsHomogeneous.sum
    intro i _
    exact isHomogeneous_vandermonde.scaleVar t i
  have hghom : g.IsHomogeneous 0 := by
    apply isHomogeneous_vandermonde.of_mul_left (vandermonde_ne_zero N K)
    simpa [Nat.add_zero, hpg] using hphom
  have hgC : g = C (g.coeff 0) := by
    calc
      g = homogeneousComponent 0 g := (homogeneousComponent_eq_self hghom).symm
      _ = C (g.coeff 0) := homogeneousComponent_zero g
  have hc : g.coeff 0 = ∑ i : Fin N, t ^ (Fin.rev i).val := by
    have hcoeff := congrArg
      (fun f : MvPolynomial (Fin N) K ↦ f.coeff (vandermondeLexExponent N)) hpg
    rw [hgC] at hcoeff
    rw [mul_comm, coeff_C_mul] at hcoeff
    simpa [p, coeff_sum, coeff_scaleVar_vandermonde, coeff_vandermonde]
      using hcoeff.symm
  change p = _
  rw [hpg, hgC, hc]
  simp [smul_eq_C_mul, mul_comm]

/-- At a `k`-th root of unity, an expanded elementary symmetric polynomial is an eigenvector
of the first Macdonald operator with the same eigenvalue as the constant polynomial. -/
theorem macdonaldD_symmetricExpandedEsymm [Field K] [CharZero K]
    (zeta t : K) (k h : ℕ) (hzeta : zeta ^ k = 1) :
    macdonaldD zeta t (PartitionDivision.symmetricExpandedEsymm (N := N) k h) =
      (∑ i : Fin N, t ^ (Fin.rev i).val) •
        PartitionDivision.symmetricExpandedEsymm k h := by
  apply Subtype.ext
  apply vandermonde_mul_injective
  change vandermonde N K *
      (↑(macdonaldD (N := N) zeta t
        (PartitionDivision.symmetricExpandedEsymm (N := N) k h)) :
          MvPolynomial (Fin N) K) =
    vandermonde N K *
      (↑(show symmetricSubalgebra (Fin N) K from
        (∑ i : Fin N, t ^ (Fin.rev i).val) •
          PartitionDivision.symmetricExpandedEsymm (N := N) k h) :
            MvPolynomial (Fin N) K)
  rw [vandermonde_mul_macdonaldD]
  change macdonaldNumerator zeta t (expand k (esymm (Fin N) K h)) =
    vandermonde N K *
      ((∑ i : Fin N, t ^ (Fin.rev i).val) • expand k (esymm (Fin N) K h))
  simp_rw [macdonaldNumerator, scaleVar_expand_of_pow_eq_one zeta k hzeta]
  rw [← Finset.sum_mul, sum_scaleVar_vandermonde]
  simp only [smul_eq_C_mul, map_sum, map_pow]
  ring

end MvPolynomial

namespace LinearAlgebra

variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- A unitriangular change of vectors can be inverted below each index. -/
theorem sub_mem_span_lower_of_unitriangular [LinearOrder ι] [WellFoundedLT ι]
    (P m : ι → V)
    (htri : ∀ a, P a - m a ∈ Submodule.span F (m '' Set.Iio a)) :
    ∀ a, P a - m a ∈ Submodule.span F (P '' Set.Iio a) := by
  intro a
  apply wellFounded_lt.induction a
  intro a ih
  refine Submodule.span_induction
    (p := fun x _ ↦ x ∈ Submodule.span F (P '' Set.Iio a))
    ?_ (Submodule.zero_mem _) ?_ ?_ (htri a)
  · intro x hx
    obtain ⟨b, hba, rfl⟩ := hx
    have hPb : P b ∈ Submodule.span F (P '' Set.Iio a) := by
      apply Submodule.subset_span
      exact ⟨b, hba, rfl⟩
    have hsub : P b - m b ∈ Submodule.span F (P '' Set.Iio a) := by
      apply Submodule.span_mono (Set.image_mono ?_)
      · exact ih b hba
      · intro c hcb
        exact hcb.trans hba
    have hmem := Submodule.sub_mem (Submodule.span F (P '' Set.Iio a)) hPb hsub
    convert hmem using 1
    abel
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    exact Submodule.smul_mem _ c hx

/-- A finite unitriangular family over linearly independent leading vectors is linearly
independent. -/
theorem linearIndependent_of_unitriangular [LinearOrder ι] [WellFoundedLT ι] [Finite ι]
    (P m : ι → V) (hm : LinearIndependent F m)
    (htri : ∀ a, P a - m a ∈ Submodule.span F (m '' Set.Iio a)) :
    LinearIndependent F P := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have hspan : Submodule.span F (Set.range P) = Submodule.span F (Set.range m) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨a, rfl⟩
      have hma : m a ∈ Submodule.span F (Set.range m) :=
        Submodule.subset_span ⟨a, rfl⟩
      have hsub : P a - m a ∈ Submodule.span F (Set.range m) := by
        apply Submodule.span_mono ?_ (htri a)
        rintro x ⟨b, _, rfl⟩
        exact ⟨b, rfl⟩
      rw [show P a = (P a - m a) + m a by abel]
      exact Submodule.add_mem _ hsub hma
    · rw [Submodule.span_le]
      rintro x ⟨a, rfl⟩
      have hPa : P a ∈ Submodule.span F (Set.range P) :=
        Submodule.subset_span ⟨a, rfl⟩
      have hsub := sub_mem_span_lower_of_unitriangular P m htri a
      have hsub' : P a - m a ∈ Submodule.span F (Set.range P) := by
        apply Submodule.span_mono ?_ hsub
        rintro x ⟨b, _, rfl⟩
        exact ⟨b, rfl⟩
      rw [show m a = P a - (P a - m a) by abel]
      exact Submodule.sub_mem _ hPa hsub'
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card ι = Module.finrank F (Submodule.span F (Set.range P))
  rw [hspan, finrank_span_eq_card hm]

/-- A vector lying below eigenvectors with eigenvalues different from its own must vanish. -/
theorem eq_of_sub_mem_span_eigenvectors [Preorder ι]
    (D : V →ₗ[F] V) (P m : ι → V) (epsilon : ι → F) (rho : ι) (c : F)
    (hP : ∀ a, D (P a) = epsilon a • P a)
    (hPc : D (P rho) = c • P rho) (hm : D (m rho) = c • m rho)
    (hspan : P rho - m rho ∈ Submodule.span F (P '' Set.Iio rho))
    (hlinear : LinearIndependent F P)
    (hgap : ∀ a, a < rho → c ≠ epsilon a) : P rho = m rho := by
  let lower := {a : ι // a < rho}
  let Q : lower → V := fun a ↦ P a
  have hset : P '' Set.Iio rho = Set.range Q := by
    ext x
    simp [Q, lower]
  rw [hset] at hspan
  obtain ⟨d, hd⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan
  have heigen : D (P rho - m rho) = c • (P rho - m rho) := by
    rw [map_sub, hPc, hm, smul_sub]
  have hsum :
      ∑ a ∈ d.support, (d a * (epsilon a - c)) • Q a = 0 := by
    calc
      ∑ a ∈ d.support, (d a * (epsilon a - c)) • Q a =
          D (d.sum fun a x ↦ x • Q a) - c • (d.sum fun a x ↦ x • Q a) := by
            rw [Finsupp.sum, map_sum, Finset.smul_sum]
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro a ha
            rw [map_smul, hP]
            simp only [Q, mul_sub, sub_smul, smul_smul]
            rw [mul_comm c (d a)]
      _ = D (P rho - m rho) - c • (P rho - m rho) := by rw [hd]
      _ = 0 := by rw [heigen, sub_self]
  have hQ : LinearIndependent F Q :=
    hlinear.comp Subtype.val Subtype.val_injective
  have hcoeff := linearIndependent_iff'.mp hQ d.support
    (fun a ↦ d a * (epsilon a - c)) hsum
  have hd0 : d = 0 := by
    apply Finsupp.support_eq_empty.mp
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hzero := hcoeff a ha
    have hne : epsilon a - c ≠ 0 := sub_ne_zero.mpr (hgap a a.property).symm
    exact Finsupp.mem_support_iff.mp ha ((mul_eq_zero.mp hzero).resolve_right hne)
  rw [hd0] at hd
  simpa using sub_eq_zero.mp hd.symm

/-- A unitriangular eigenvector equals its leading vector when no lower eigenvalue agrees. -/
theorem eq_of_unitriangular_eigenvectors [LinearOrder ι] [WellFoundedLT ι] [Finite ι]
    (D : V →ₗ[F] V) (P m : ι → V) (epsilon : ι → F) (rho : ι) (c : F)
    (htri : ∀ a, P a - m a ∈ Submodule.span F (m '' Set.Iio a))
    (hP : ∀ a, D (P a) = epsilon a • P a)
    (hPc : D (P rho) = c • P rho) (hm : D (m rho) = c • m rho)
    (hmlinear : LinearIndependent F m)
    (hgap : ∀ a, a < rho → c ≠ epsilon a) : P rho = m rho := by
  apply eq_of_sub_mem_span_eigenvectors D P m epsilon rho c hP hPc hm
    (sub_mem_span_lower_of_unitriangular P m htri rho)
    (linearIndependent_of_unitriangular P m hmlinear htri) hgap

end LinearAlgebra

namespace PartitionDivision.Macdonald

open MvPolynomial Nat.PartitionVector Nat.PartitionVector.Pieri Polynomial

variable {N k : ℕ}

/-- Scalar multiplication multiplies the total size of a partition vector. -/
theorem partitionVectorDegree_nsmul (a : ℕ) (lambda : Nat.PartitionVector N) :
    partitionVectorDegree (a • lambda) = a * partitionVectorDegree lambda := by
  simp [partitionVectorDegree, Finset.mul_sum]

/-- The size of the initial zero-one column is its height. -/
theorem partitionVectorDegree_prefixOnes {h : ℕ} (hh : h ≤ N) :
    partitionVectorDegree (prefixOnes (N := N) h) = h := by
  simp only [partitionVectorDegree, prefixOnes_apply, Finset.sum_boole, Nat.cast_id]
  rw [Fin.card_filter_val_lt]
  exact Nat.min_eq_right hh

/-- The rectangle `prefixOnes h` is lexicographically least among partition vectors of size
`h`, provided `h` does not exceed the number of coordinates. -/
theorem not_lexKey_lt_prefixOnes_of_degree {lambda : Nat.PartitionVector N} {h : ℕ}
    (hdegree : partitionVectorDegree lambda = h) :
    ¬lexKey lambda < lexKey (prefixOnes h) := by
  intro hlex
  change Pi.Lex (· < ·) (· < ·) lambda (prefixOnes h) at hlex
  obtain ⟨i, hbefore, hi⟩ := hlex
  have hih : i.val < h := by
    rw [prefixOnes_apply] at hi
    split at hi
    · assumption
    · lia
  have hli : lambda i = 0 := by
    simp only [prefixOnes_apply, hih, reduceIte] at hi
    lia
  have hparts (j : Fin N) : lambda j = if j < i then 1 else 0 := by
    split_ifs with hji
    · have hjh : j.val < h := (Fin.mk_lt_mk.mp hji).trans hih
      rw [hbefore j hji, prefixOnes_apply]
      simp only [hjh, reduceIte]
    · have hij : i ≤ j := not_lt.mp hji
      exact Nat.eq_zero_of_le_zero (hli ▸ lambda.antitone hij)
  have hsum : partitionVectorDegree lambda = i.val := by
    rw [partitionVectorDegree]
    calc
      ∑ j, lambda j = ∑ j : Fin N, if j < i then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        exact hparts j
      _ = i.val := by
        have hf : (Finset.univ.filter fun j : Fin N ↦ j < i) = Finset.Iio i := by
          ext j
          simp
        calc
          (∑ j : Fin N, if j < i then 1 else 0) =
              (Finset.univ.filter fun j : Fin N ↦ j < i).card := by
                exact_mod_cast
                  (Finset.sum_boole (R := ℕ) (fun j : Fin N ↦ j < i) Finset.univ)
          _ = (Finset.Iio i).card := congrArg Finset.card hf
          _ = i.val := Fin.card_Iio i
  rw [hdegree] at hsum
  lia

/-- Coordinatewise divisibility by `k` lets a partition vector be divided by `k`. -/
theorem exists_smul_eq_of_forall_dvd (alpha : Nat.PartitionVector N)
    (hdiv : ∀ i, k ∣ alpha i) :
    ∃ beta : Nat.PartitionVector N, k • beta = alpha := by
  let beta : Nat.PartitionVector N :=
    ⟨fun i ↦ alpha i / k, fun i j hij ↦ Nat.div_le_div_right (alpha.antitone hij)⟩
  refine ⟨beta, ?_⟩
  apply Nat.PartitionVector.ext
  intro i
  change k * (alpha i / k) = alpha i
  exact Nat.mul_div_cancel' (hdiv i)

/-- A positive multiple of `prefixOnes h` has no smaller partition vector of the same size whose
coordinates are all divisible by the multiplier. -/
theorem not_lexKey_lt_smul_prefixOnes_of_degree_of_dvd (hk : 0 < k)
    {alpha : Nat.PartitionVector N} {h : ℕ}
    (hdegree : partitionVectorDegree alpha = k * h)
    (hlex : lexKey alpha < lexKey (k • prefixOnes h))
    (hdiv : ∀ i, k ∣ alpha i) : False := by
  obtain ⟨beta, rfl⟩ := exists_smul_eq_of_forall_dvd alpha hdiv
  have hbetaDegree : partitionVectorDegree beta = h := by
    rw [partitionVectorDegree_nsmul] at hdegree
    exact Nat.eq_of_mul_eq_mul_left hk hdegree
  have hbetaLex : lexKey beta < lexKey (prefixOnes h) := by
    change Pi.Lex (· < ·) (· < ·) (k • beta) (k • prefixOnes h) at hlex
    change Pi.Lex (· < ·) (· < ·) beta (prefixOnes h)
    obtain ⟨i, hbefore, hi⟩ := hlex
    refine ⟨i, fun j hji ↦ ?_, ?_⟩
    · exact Nat.eq_of_mul_eq_mul_left hk (hbefore j hji)
    · exact (Nat.mul_lt_mul_left hk).mp hi
  exact not_lexKey_lt_prefixOnes_of_degree hbetaDegree hbetaLex

/-- The polynomial in `v` whose image in `L(v)` is the specialized first Macdonald
eigenvalue. -/
def rootEigenvaluePolynomial {L : Type*} [Field L] (zeta : L)
    (alpha : Nat.PartitionVector N) : L[X] :=
  ∑ i : Fin N, Polynomial.C (zeta ^ (alpha i + (Fin.rev i).val)) *
    Polynomial.X ^ (Fin.rev i).val

/-- The coefficient of the power indexed by a row in the root eigenvalue polynomial. -/
theorem coeff_rootEigenvaluePolynomial {L : Type*} [Field L] (zeta : L)
    (alpha : Nat.PartitionVector N) (i : Fin N) :
    (rootEigenvaluePolynomial zeta alpha).coeff (Fin.rev i).val =
      zeta ^ (alpha i + (Fin.rev i).val) := by
  classical
  rw [rootEigenvaluePolynomial]
  let f : Fin N → L[X] := fun j ↦
    Polynomial.C (zeta ^ (alpha j + (Fin.rev j).val)) *
      Polynomial.X ^ (Fin.rev j).val
  have hsum : (∑ j : Fin N, f j).coeff (Fin.rev i).val =
      ∑ j : Fin N, (f j).coeff (Fin.rev i).val := by
    simp
  change (∑ j : Fin N, f j).coeff (Fin.rev i).val = _
  rw [hsum, Finset.sum_eq_single i]
  · rw [show f i = Polynomial.C
        (zeta ^ (alpha i + (Fin.rev i).val)) * Polynomial.X ^ (Fin.rev i).val by rfl]
    rw [Polynomial.coeff_C_mul_X_pow]
    rw [ite_eq_left rfl]
  · intro j _ hji
    have hrev : (Fin.rev j).val ≠ (Fin.rev i).val := by
      intro h
      apply hji
      apply Fin.rev_injective
      exact Fin.ext h
    rw [show f j = Polynomial.C
        (zeta ^ (alpha j + (Fin.rev j).val)) * Polynomial.X ^ (Fin.rev j).val by rfl]
    rw [Polynomial.coeff_C_mul_X_pow]
    rw [ite_eq_right_iff]
    exact fun h ↦ (hrev.symm h).elim
  · simp

/-- Mapping the root eigenvalue polynomial to the fraction field gives the Macdonald
eigenvalue at `q = zeta`, `t = zeta v`. -/
theorem algebraMap_rootEigenvaluePolynomial {L : Type*} [Field L] (zeta : L)
    (alpha : Nat.PartitionVector N) :
    algebraMap L[X] (RationalFunction L) (rootEigenvaluePolynomial zeta alpha) =
      macdonaldEigenvalue (N := N) (constantRationalFunction zeta)
        (scaledVariableRationalFunction zeta) alpha := by
  simp only [rootEigenvaluePolynomial, macdonaldEigenvalue, constantRationalFunction,
    scaledVariableRationalFunction, pow_add, map_sum, map_mul, map_pow, mul_pow]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Below the rectangular index, the specialized first-operator eigenvalue is different from
the rectangular eigenvalue. -/
theorem macdonaldEigenvalue_ne_smul_prefixOnes {L : Type*} [Field L] [CharZero L]
    (zeta : L) (hprimitive : IsPrimitiveRoot zeta k) (hk : 0 < k)
    {alpha : Nat.PartitionVector N} {h : ℕ}
    (hdegree : partitionVectorDegree alpha = k * h)
    (hlex : lexKey alpha < lexKey (k • prefixOnes h)) :
    macdonaldEigenvalue (N := N) (constantRationalFunction zeta)
        (scaledVariableRationalFunction zeta) alpha ≠
      macdonaldEigenvalue (N := N) (constantRationalFunction zeta)
        (scaledVariableRationalFunction zeta) (k • prefixOnes (N := N) h) := by
  intro heq
  have hpoly : rootEigenvaluePolynomial zeta alpha =
      rootEigenvaluePolynomial zeta (k • prefixOnes (N := N) h) := by
    apply IsFractionRing.injective L[X] (RationalFunction L)
    rw [algebraMap_rootEigenvaluePolynomial, algebraMap_rootEigenvaluePolynomial]
    simpa [macdonaldEigenvalue, Nat.PartitionVector.smul_apply] using heq
  have hzeta : zeta ≠ 0 := (hprimitive.isUnit hk.ne').ne_zero
  have hdiv (i : Fin N) : k ∣ alpha i := by
    have hcoeff := congrArg (fun p : L[X] ↦ p.coeff (Fin.rev i).val) hpoly
    rw [coeff_rootEigenvaluePolynomial, coeff_rootEigenvaluePolynomial] at hcoeff
    have hrect : (k • prefixOnes h) i = k * prefixOnes h i := rfl
    rw [hrect, pow_add, pow_add] at hcoeff
    have hkpow : zeta ^ (k * prefixOnes h i) = 1 := by
      rw [pow_mul, hprimitive.pow_eq_one, one_pow]
    rw [hkpow, one_mul] at hcoeff
    have hpow : zeta ^ alpha i = 1 := by
      apply mul_right_cancel₀ (pow_ne_zero _ hzeta)
      simpa only [one_mul] using hcoeff
    exact (hprimitive.pow_eq_one_iff_dvd _).mp hpow
  exact not_lexKey_lt_smul_prefixOnes_of_degree_of_dvd hk hdegree hlex hdiv

/-- A monomial symmetric polynomial, packaged in the symmetric subalgebra. -/
def symmetricMsymmVec (F : Type*) [Field F] (lambda : Nat.PartitionVector N) :
    symmetricSubalgebra (Fin N) F :=
  ⟨msymmVec F lambda, msymmVec_isSymmetric F lambda⟩

private def initialFinset (N h : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ i.val < h

private theorem finsetSum_single_one_apply (s : Finset (Fin N)) (i : Fin N) :
    (∑ j ∈ s, Finsupp.single j 1) i = if i ∈ s then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      change (Finsupp.single a 1) i + (∑ j ∈ s, Finsupp.single j 1) i = _
      rw [ih]
      by_cases hia : i = a
      · subst a
        simp [ha]
      · simp [hia]

private theorem subset_eq_initialFinset_of_exponent_eq_partition
    {s : Finset (Fin N)} {h : ℕ} {mu : Nat.PartitionVector N}
    (hk : 0 < k) (hs : s.card = h)
    (heq : k • (∑ i ∈ s, Finsupp.single i 1) = partitionVectorFinsupp mu) :
    s = initialFinset N h ∧ mu = k • prefixOnes h := by
  have hcoord (i : Fin N) : mu i = if i ∈ s then k else 0 := by
    have hi := congrArg (fun d : Fin N →₀ ℕ ↦ d i) heq
    change k * (∑ j ∈ s, Finsupp.single j 1) i = mu i at hi
    rw [finsetSum_single_one_apply] at hi
    simpa [mul_ite] using hi.symm
  have hdown {i j : Fin N} (hij : i ≤ j) (hj : j ∈ s) : i ∈ s := by
    by_contra hi
    have hanti := mu.antitone hij
    rw [hcoord i, hcoord j] at hanti
    simp only [hi, hj, ↓reduceIte] at hanti
    lia
  have hsinitial : s = initialFinset N h := by
    ext j
    simp only [initialFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      have hsubset : Finset.Iic j ⊆ s := fun i hi ↦ hdown (Finset.mem_Iic.mp hi) hj
      have hcard := Finset.card_le_card hsubset
      rw [Fin.card_Iic, hs] at hcard
      lia
    · intro hj
      by_contra hjs
      have hsubset : s ⊆ Finset.Iio j := by
        intro i hi
        rw [Finset.mem_Iio]
        by_contra hji
        exact hjs (hdown (not_lt.mp hji) hi)
      have hcard := Finset.card_le_card hsubset
      rw [hs, Fin.card_Iio] at hcard
      lia
  refine ⟨hsinitial, ?_⟩
  apply Nat.PartitionVector.ext
  intro i
  rw [hcoord, hsinitial]
  simp [initialFinset, prefixOnes_apply, Nat.PartitionVector.smul_apply]

private theorem subsetExponent_eq_partitionVectorFinsupp_iff
    {s : Finset (Fin N)} {h : ℕ} {mu : Nat.PartitionVector N}
    (hk : 0 < k) (hs : s.card = h) :
    k • (∑ i ∈ s, Finsupp.single i 1) = partitionVectorFinsupp mu ↔
      s = initialFinset N h ∧ mu = k • prefixOnes h := by
  constructor
  · exact subset_eq_initialFinset_of_exponent_eq_partition hk hs
  · rintro ⟨rfl, rfl⟩
    ext i
    change k * (∑ j ∈ initialFinset N h, Finsupp.single j 1) i =
      (k • prefixOnes h) i
    rw [finsetSum_single_one_apply]
    simp [initialFinset, prefixOnes_apply, Nat.PartitionVector.smul_apply, mul_ite]

/-- The monomial symmetric polynomial of a rectangle is the corresponding expanded elementary
symmetric polynomial. -/
theorem symmetricMsymmVec_smul_prefixOnes_eq_symmetricExpandedEsymm
    {F : Type*} [Field F] (hk : 0 < k) {h : ℕ} (hh : h ≤ N) :
    symmetricMsymmVec F (k • prefixOnes (N := N) h) =
      symmetricExpandedEsymm (F := F) (N := N) k h := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_isSymmetric_of_coeff_eq_zero
  · exact (msymmVec_isSymmetric F _).sub ((esymm_isSymmetric (Fin N) F h).expand k)
  · intro mu
    change (msymmVec F (k • prefixOnes h)).coeff (partitionVectorFinsupp mu) -
        (expand k (esymm (Fin N) F h)).coeff (partitionVectorFinsupp mu) = 0
    rw [coeff_msymmVec_partitionVectorFinsupp, sub_eq_zero]
    change (if mu = k • prefixOnes h then 1 else 0) =
      (expand k (esymm (Fin N) F h)).coeff (partitionVectorFinsupp mu)
    rw [esymm_eq_sum_monomial, map_sum, MvPolynomial.coeff_sum]
    simp_rw [expand_monomial, MvPolynomial.coeff_monomial]
    classical
    by_cases hmu : mu = k • prefixOnes h
    · simp only [hmu, ↓reduceIte]
      rw [Finset.sum_eq_single (initialFinset N h)]
      · have heq := (subsetExponent_eq_partitionVectorFinsupp_iff hk
          (by simp [initialFinset, Fin.card_filter_val_lt, Nat.min_eq_right hh])).2
          ⟨rfl, hmu⟩
        have heq' := heq.trans (congrArg partitionVectorFinsupp hmu)
        simp only [heq', ↓reduceIte]
      · intro s hs hne
        simp only [ite_eq_right_iff, one_ne_zero, imp_false]
        intro heq
        exact hne ((subsetExponent_eq_partitionVectorFinsupp_iff hk
          (Finset.mem_powersetCard.mp hs).2).1 heq).1
      · intro hnot
        exfalso
        apply hnot
        rw [Finset.mem_powersetCard]
        simp [initialFinset, Fin.card_filter_val_lt, Nat.min_eq_right hh]
    · simp only [hmu, ↓reduceIte]
      symm
      apply Finset.sum_eq_zero
      intro s hs
      simp only [ite_eq_right_iff, one_ne_zero, imp_false]
      intro heq
      exact hmu ((subsetExponent_eq_partitionVectorFinsupp_iff hk
        (Finset.mem_powersetCard.mp hs).2).1 heq).2

/-- The first-operator argument yields the rectangle identities from homogeneous
lex-unitriangularity and the expected Macdonald eigenvalues. -/
theorem satisfiesRectangles_of_macdonaldD_eigenvectors
    {L : Type*} [Field L] [CharZero L]
    (zeta : L) (hprimitive : IsPrimitiveRoot zeta k) (hk : 0 < k)
    (P : Module.Basis (Nat.PartitionVector N) (RationalFunction L)
      (symmetricSubalgebra (Fin N) (RationalFunction L)))
    (htri : ∀ lambda,
      P lambda - symmetricMsymmVec (RationalFunction L) lambda ∈
        Submodule.span (RationalFunction L)
          (symmetricMsymmVec (RationalFunction L) ''
            {mu | partitionVectorDegree mu = partitionVectorDegree lambda ∧
              lexKey mu < lexKey lambda}))
    (heigen : ∀ lambda,
      macdonaldD (constantRationalFunction zeta) (scaledVariableRationalFunction zeta)
          (P lambda) =
        macdonaldEigenvalue (constantRationalFunction zeta)
          (scaledVariableRationalFunction zeta) lambda • P lambda) :
    SatisfiesRectangles P k := by
  intro h _ hh
  let F := RationalFunction L
  let rho : Nat.PartitionVector N := k • prefixOnes h
  let I := {lambda : Nat.PartitionVector N // partitionVectorDegree lambda = k * h}
  let rhoI : I := ⟨rho, by
    simp [rho, partitionVectorDegree_nsmul, partitionVectorDegree_prefixOnes hh]⟩
  let pI : I → symmetricSubalgebra (Fin N) F := fun lambda ↦ P lambda.1
  let mI : I → symmetricSubalgebra (Fin N) F := fun lambda ↦
    symmetricMsymmVec F lambda.1
  let epsilon : I → F := fun lambda ↦
    macdonaldEigenvalue (constantRationalFunction zeta)
      (scaledVariableRationalFunction zeta) lambda.1
  let _ : LinearOrder I := LinearOrder.lift' (fun lambda : I ↦ lexKey lambda.1)
    (lexKey_injective.comp Subtype.val_injective)
  let _ : WellFoundedLT I := by
    change WellFounded (InvImage (· < ·) (fun lambda : I ↦ lexKey lambda.1))
    exact InvImage.wf (fun lambda : I ↦ lexKey lambda.1) wellFounded_lt
  have htriI (lambda : I) :
      pI lambda - mI lambda ∈
        Submodule.span F (mI '' Set.Iio lambda) := by
    have h := htri lambda.1
    apply Submodule.span_mono ?_ h
    intro x hx
    obtain ⟨mu, hmu, rfl⟩ := hx
    refine ⟨⟨mu, hmu.1.trans lambda.2⟩, ?_, rfl⟩
    exact hmu.2
  have hlinear : LinearIndependent F pI :=
    P.linearIndependent.comp Subtype.val Subtype.val_injective
  have hrootFraction : (constantRationalFunction zeta) ^ k = 1 := by
    change (algebraMap L[X] (RationalFunction L) (Polynomial.C zeta)) ^ k = 1
    rw [← map_pow, ← Polynomial.C_pow, hprimitive.pow_eq_one]
    exact map_one _
  have hc : epsilon rhoI = ∑ i : Fin N,
      scaledVariableRationalFunction zeta ^ (Fin.rev i).val := by
    simp only [epsilon, rhoI, rho, macdonaldEigenvalue]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.PartitionVector.smul_apply, pow_mul]
    rw [hrootFraction, one_pow, one_mul]
  have hP : ∀ lambda, macdonaldD (constantRationalFunction zeta)
      (scaledVariableRationalFunction zeta) (pI lambda) =
        epsilon lambda • pI lambda := by
    intro lambda
    exact heigen lambda.1
  have hPc : macdonaldD (constantRationalFunction zeta)
      (scaledVariableRationalFunction zeta) (pI rhoI) =
        (∑ i : Fin N, scaledVariableRationalFunction zeta ^ (Fin.rev i).val) •
          pI rhoI := by
    rw [hP, hc]
  have hm : macdonaldD (constantRationalFunction zeta)
      (scaledVariableRationalFunction zeta) (mI rhoI) =
        (∑ i : Fin N, scaledVariableRationalFunction zeta ^ (Fin.rev i).val) •
          mI rhoI := by
    have hmrect : mI rhoI = symmetricExpandedEsymm k h := by
      exact symmetricMsymmVec_smul_prefixOnes_eq_symmetricExpandedEsymm hk hh
    rw [hmrect]
    exact MvPolynomial.macdonaldD_symmetricExpandedEsymm
      (constantRationalFunction zeta) (scaledVariableRationalFunction zeta) k h hrootFraction
  have hgap : ∀ lambda : I, lambda < rhoI →
      (∑ i : Fin N, scaledVariableRationalFunction zeta ^ (Fin.rev i).val) ≠
        epsilon lambda := by
    intro lambda hlambda heq
    apply macdonaldEigenvalue_ne_smul_prefixOnes zeta hprimitive hk lambda.2 hlambda
    change epsilon lambda = epsilon rhoI
    exact heq.symm.trans hc.symm
  have heq := LinearAlgebra.eq_of_sub_mem_span_eigenvectors
    (macdonaldD (constantRationalFunction zeta) (scaledVariableRationalFunction zeta))
    pI mI epsilon rhoI
    (∑ i : Fin N, scaledVariableRationalFunction zeta ^ (Fin.rev i).val)
    hP hPc hm (LinearAlgebra.sub_mem_span_lower_of_unitriangular pI mI htriI rhoI)
    hlinear hgap
  change P rho = symmetricExpandedEsymm k h
  rw [← symmetricMsymmVec_smul_prefixOnes_eq_symmetricExpandedEsymm hk hh]
  exact heq

end PartitionDivision.Macdonald
