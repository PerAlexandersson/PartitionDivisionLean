/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.LinearAlgebra.Basis.Basic
public import PartitionDivision.Mathlib.RingTheory.MvPolynomial.Symmetric.Monomial

/-!
# The monomial basis of symmetric polynomials in finitely many variables

For an exponent vector `d : Fin N → ℕ`, `Nat.PartitionVector.sortDesc d` is its decreasing
rearrangement.  It is the unique partition vector whose rearrangement orbit contains `d`, and it
is the lexicographically largest element of that orbit.

Consequently every symmetric polynomial is the finite sum of its coefficients times the
monomial symmetric polynomials `msymmVec`, and the `msymmVec μ` with `μ` of size `n` form a
basis of the symmetric polynomials that are homogeneous of degree `n`.

## Main declarations

* `Nat.PartitionVector.sortDesc`: the decreasing rearrangement of a vector.
* `MvPolynomial.mem_partitionVectorRearrangements_iff_sortDesc_eq`: orbit membership is
  determined by the decreasing rearrangement.
* `MvPolynomial.toLex_le_partitionVectorFinsupp_of_mem`: a partition vector is the
  lexicographically largest element of its rearrangement orbit.
* `MvPolynomial.IsSymmetric.eq_sum_msymmVec`, `MvPolynomial.IsSymmetric.mem_span_msymmVec`:
  the expansion of a symmetric polynomial in the monomial symmetric polynomials.
* `MvPolynomial.symmetricHomogeneousSubmodule` and `MvPolynomial.msymmVecBasis`: the
  homogeneous symmetric polynomials of a fixed degree and their monomial basis.
-/

@[expose] public section

noncomputable section

open Finset

namespace Nat.PartitionVector

variable {N : ℕ}

/-- The permutation sorting a vector decreasingly: `d ∘ sortDescPerm d` is antitone. -/
def sortDescPerm (d : Fin N → ℕ) : Equiv.Perm (Fin N) :=
  Fin.revPerm.trans (Tuple.sort d)

/-- The decreasing rearrangement of a vector of natural numbers. -/
def sortDesc (d : Fin N → ℕ) : PartitionVector N :=
  ⟨d ∘ sortDescPerm d, fun _ _ hij ↦ Tuple.monotone_sort d (Fin.rev_anti hij)⟩

theorem sortDesc_apply (d : Fin N → ℕ) (i : Fin N) : sortDesc d i = d (sortDescPerm d i) :=
  rfl

end Nat.PartitionVector

namespace MvPolynomial

open Nat.PartitionVector

variable {N : ℕ}

/-- The finitely supported exponent vector of a partition vector has the same coordinates. -/
@[simp]
theorem coe_partitionVectorFinsupp (lambda : Nat.PartitionVector N) :
    ⇑(partitionVectorFinsupp lambda) = lambda :=
  funext (partitionVectorFinsupp_apply lambda)

/-- Every exponent vector lies in the rearrangement orbit of its decreasing rearrangement. -/
theorem mem_partitionVectorRearrangements_sortDesc (d : Fin N →₀ ℕ) :
    d ∈ partitionVectorRearrangements (sortDesc d) := by
  rw [mem_partitionVectorRearrangements_iff]
  refine ⟨sortDescPerm d, ?_⟩
  ext i
  rw [Finsupp.mapDomain_equiv_apply, partitionVectorFinsupp_apply, sortDesc_apply,
    Equiv.apply_symm_apply]

/-- An exponent vector lies in the orbit of a partition vector exactly when that partition
vector is its decreasing rearrangement. -/
theorem mem_partitionVectorRearrangements_iff_sortDesc_eq
    (lambda : Nat.PartitionVector N) (d : Fin N →₀ ℕ) :
    d ∈ partitionVectorRearrangements lambda ↔ sortDesc d = lambda := by
  constructor
  · intro hd
    have hs := mem_partitionVectorRearrangements_sortDesc d
    rw [mem_partitionVectorRearrangements_iff] at hd hs
    obtain ⟨e, he⟩ := hd
    obtain ⟨f, hf⟩ := hs
    rw [← partitionVectorFinsupp_mem_rearrangements_iff, mem_partitionVectorRearrangements_iff]
    refine ⟨e.trans f.symm, ?_⟩
    ext i
    have h1 := congrArg (fun x : Fin N →₀ ℕ ↦ x (f i)) he
    have h2 := congrArg (fun x : Fin N →₀ ℕ ↦ x (f i)) hf
    simp only [Finsupp.mapDomain_equiv_apply, partitionVectorFinsupp_apply,
      Equiv.symm_apply_apply] at h1 h2 ⊢
    simp only [Equiv.symm_trans_apply, Equiv.symm_symm]
    rw [h1, ← h2]
  · rintro rfl
    exact mem_partitionVectorRearrangements_sortDesc d

/-- The decreasing rearrangement of a partition vector is itself. -/
@[simp]
theorem sortDesc_partitionVectorFinsupp (lambda : Nat.PartitionVector N) :
    sortDesc (partitionVectorFinsupp lambda) = lambda := by
  rw [← mem_partitionVectorRearrangements_iff_sortDesc_eq,
    partitionVectorFinsupp_mem_rearrangements_iff]

/-- A decreasing vector is the unique antitone rearrangement of `d`. -/
theorem eq_sortDesc_of_mem {lambda : Nat.PartitionVector N} {d : Fin N →₀ ℕ}
    (hd : d ∈ partitionVectorRearrangements lambda) : lambda = sortDesc d :=
  ((mem_partitionVectorRearrangements_iff_sortDesc_eq lambda d).mp hd).symm

/-- Permuting the coordinates of an exponent vector does not change its decreasing
rearrangement. -/
theorem sortDesc_mapDomain (e : Equiv.Perm (Fin N)) (d : Fin N →₀ ℕ) :
    sortDesc (d.mapDomain e) = sortDesc d := by
  rw [← mem_partitionVectorRearrangements_iff_sortDesc_eq,
    mapDomain_mem_partitionVectorRearrangements_iff]
  exact mem_partitionVectorRearrangements_sortDesc d

/-- A partition vector is the lexicographically largest element of its rearrangement orbit. -/
theorem toLex_le_partitionVectorFinsupp_of_mem {lambda : Nat.PartitionVector N}
    {d : Fin N →₀ ℕ} (hd : d ∈ partitionVectorRearrangements lambda) :
    toLex d ≤ toLex (partitionVectorFinsupp lambda) := by
  classical
  rw [mem_partitionVectorRearrangements_iff] at hd
  obtain ⟨e, rfl⟩ := hd
  have happ (i : Fin N) :
      (partitionVectorFinsupp lambda).mapDomain e i = lambda (e.symm i) := by
    rw [Finsupp.mapDomain_equiv_apply, partitionVectorFinsupp_apply]
  rw [← not_lt, Finsupp.Lex.lt_iff]
  rintro ⟨i, hlow, hi⟩
  simp only [ofLex_toLex, partitionVectorFinsupp_apply, happ] at hlow hi
  have hsub : Finset.univ.filter (fun j ↦ lambda i < lambda j) ⊂
      Finset.univ.filter (fun j ↦ lambda i < lambda (e.symm j)) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨i, by simpa using hi, by simp⟩
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have hji : j < i := by
        by_contra hle
        exact (lambda.antitone (not_lt.mp hle)).not_gt hj
      rwa [← hlow j hji]
  have hcard : #(Finset.univ.filter (fun j ↦ lambda i < lambda (e.symm j))) =
      #(Finset.univ.filter (fun j ↦ lambda i < lambda j)) :=
    Finset.card_equiv e.symm (by simp)
  exact (Finset.card_lt_card hsub).ne hcard.symm

variable {R : Type*} [CommSemiring R]

/-- A symmetric polynomial has the same coefficient at an exponent vector and at its decreasing
rearrangement. -/
theorem IsSymmetric.coeff_sortDesc {f : MvPolynomial (Fin N) R} (hf : f.IsSymmetric)
    (d : Fin N →₀ ℕ) : f.coeff (partitionVectorFinsupp (sortDesc d)) = f.coeff d := by
  obtain ⟨e, he⟩ := (mem_partitionVectorRearrangements_iff _ _).mp
    (mem_partitionVectorRearrangements_sortDesc d)
  conv_rhs => rw [← he]
  rw [← coeff_rename_mapDomain e e.injective f, hf e]

/-- A symmetric polynomial is the sum of its coefficients at decreasing exponent vectors times
the corresponding monomial symmetric polynomials. -/
theorem IsSymmetric.eq_sum_msymmVec {f : MvPolynomial (Fin N) R} (hf : f.IsSymmetric) :
    f = ∑ mu ∈ f.support.image fun d : Fin N →₀ ℕ ↦ sortDesc d,
      f.coeff (partitionVectorFinsupp mu) • msymmVec R mu := by
  classical
  ext d
  rw [coeff_sum]
  simp_rw [coeff_smul, coeff_msymmVec, mem_partitionVectorRearrangements_iff_sortDesc_eq,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, hf.coeff_sortDesc]
  split_ifs with h
  · rfl
  · simp only [Finset.mem_image, not_exists, not_and] at h
    by_contra hne
    exact h d (mem_support_iff.mpr hne) rfl

/-- A symmetric polynomial lies in the span of the monomial symmetric polynomials indexed by any
set containing every partition vector in its support. -/
theorem IsSymmetric.mem_span_msymmVec {f : MvPolynomial (Fin N) R} (hf : f.IsSymmetric)
    {S : Set (Nat.PartitionVector N)}
    (hS : ∀ mu, partitionVectorFinsupp mu ∈ f.support → mu ∈ S) :
    f ∈ Submodule.span R (msymmVec R '' S) := by
  rw [hf.eq_sum_msymmVec]
  refine Submodule.sum_mem _ fun mu hmu ↦ Submodule.smul_mem _ _
    (Submodule.subset_span ⟨mu, hS mu ?_, rfl⟩)
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hmu
  rw [mem_support_iff, hf.coeff_sortDesc]
  exact mem_support_iff.mp hd

/-- A partition vector in the support of a homogeneous polynomial has the polynomial's
degree as its size. -/
theorem IsHomogeneous.partitionVectorDegree_eq {f : MvPolynomial (Fin N) R} {n : ℕ}
    (hf : f.IsHomogeneous n) {mu : Nat.PartitionVector N}
    (hmu : partitionVectorFinsupp mu ∈ f.support) : partitionVectorDegree mu = n := by
  rw [← degree_eq_partitionVectorDegree_of_mem mu
    ((partitionVectorFinsupp_mem_rearrangements_iff mu mu).mpr rfl),
    Finsupp.degree_eq_weight_one]
  exact hf (mem_support_iff.mp hmu)

variable (R) in
/-- The symmetric polynomials that are homogeneous of degree `n`. -/
def symmetricHomogeneousSubmodule (σ : Type*) (n : ℕ) : Submodule R (MvPolynomial σ R) :=
  Subalgebra.toSubmodule (symmetricSubalgebra σ R) ⊓ homogeneousSubmodule σ R n

theorem mem_symmetricHomogeneousSubmodule {σ : Type*} {n : ℕ} {f : MvPolynomial σ R} :
    f ∈ symmetricHomogeneousSubmodule R σ n ↔ f.IsSymmetric ∧ f.IsHomogeneous n := by
  simp [symmetricHomogeneousSubmodule, mem_homogeneousSubmodule]

/-- There are finitely many partition vectors of a fixed size. -/
instance finite_partitionVectorDegree (n : ℕ) :
    Finite {mu : Nat.PartitionVector N // partitionVectorDegree mu = n} := by
  have hle (mu : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n}) (i : Fin N) :
      mu.1 i < n + 1 := by
    have h : mu.1 i ≤ ∑ j, mu.1 j :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hn : ∑ j, mu.1 j = n := mu.2
    lia
  refine Finite.of_injective (fun mu i ↦ (⟨mu.1 i, hle mu i⟩ : Fin (n + 1))) ?_
  intro mu nu h
  apply Subtype.ext
  apply Nat.PartitionVector.ext
  intro i
  have := congrFun h i
  simpa using this

variable (K : Type*) [Field K]

/-- The monomial symmetric polynomials of size `n` span the homogeneous symmetric polynomials of
degree `n`. -/
theorem span_msymmVec_partitionVectorDegree_eq (N n : ℕ) :
    Submodule.span K (Set.range (msymmVec K ∘
      (Subtype.val : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n} →
        Nat.PartitionVector N))) =
      symmetricHomogeneousSubmodule K (Fin N) n := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨mu, rfl⟩
    rw [SetLike.mem_coe, mem_symmetricHomogeneousSubmodule]
    have h := isHomogeneous_msymmVec K mu.1
    rw [mu.2] at h
    exact ⟨msymmVec_isSymmetric K mu.1, h⟩
  · intro f hf
    rw [mem_symmetricHomogeneousSubmodule] at hf
    have h := hf.1.mem_span_msymmVec (S := {mu | partitionVectorDegree mu = n})
      (fun mu hmu ↦ hf.2.partitionVectorDegree_eq hmu)
    refine Submodule.span_mono ?_ h
    rintro _ ⟨mu, hmu, rfl⟩
    exact ⟨⟨mu, hmu⟩, rfl⟩

/-- The monomial basis of the homogeneous symmetric polynomials of degree `n`. -/
def msymmVecBasis (N n : ℕ) :
    Module.Basis {mu : Nat.PartitionVector N // partitionVectorDegree mu = n} K
      (symmetricHomogeneousSubmodule K (Fin N) n) :=
  (Module.Basis.span ((linearIndependent_msymmVec K).comp Subtype.val
    Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (span_msymmVec_partitionVectorDegree_eq K N n))

@[simp]
theorem coe_msymmVecBasis (N n : ℕ)
    (mu : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n}) :
    (msymmVecBasis K N n mu : MvPolynomial (Fin N) K) = msymmVec K mu.1 := by
  simp [msymmVecBasis, Module.Basis.span_apply]

end MvPolynomial
