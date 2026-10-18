/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Data.Fin.Tuple.Sort
public import PartitionDivision.Mathlib.Combinatorics.Enumerative.Partition.Restricted

/-!
# Monomial symmetric polynomials indexed by partition vectors

This file defines `MvPolynomial.msymmVec K λ`, the sum of the monomials `x^d` over the distinct
rearrangements `d` of a partition vector `λ`, and proves that it is symmetric and homogeneous,
computes its coefficients, and shows that these polynomials are linearly independent.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

open Finset Multiset Sym

variable {R σ : Type*} [CommSemiring R]

/-- The finitely supported exponent vector underlying a partition vector. -/
def partitionVectorFinsupp {N : ℕ} (lambda : Nat.PartitionVector N) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm lambda

@[simp]
theorem partitionVectorFinsupp_apply {N : ℕ} (lambda : Nat.PartitionVector N)
    (i : Fin N) : partitionVectorFinsupp lambda i = lambda i := by
  exact congrFun (Finsupp.equivFunOnFinite.apply_symm_apply lambda) i

/-- The total size of a partition vector. -/
def partitionVectorDegree {N : ℕ} (lambda : Nat.PartitionVector N) : ℕ :=
  ∑ i, lambda i

/-- The distinct rearrangements of a partition vector, represented as exponent vectors. -/
def partitionVectorRearrangements {N : ℕ} (lambda : Nat.PartitionVector N) :
    Finset (Fin N →₀ ℕ) := by
  classical
  let _ := Fintype.ofFinite (Equiv.Perm (Fin N))
  exact Finset.univ.image fun e : Equiv.Perm (Fin N) ↦
    (partitionVectorFinsupp lambda).mapDomain e

/-- Membership in the rearrangement orbit is witnessed by a permutation. -/
theorem mem_partitionVectorRearrangements_iff {N : ℕ}
    (lambda : Nat.PartitionVector N) (d : Fin N →₀ ℕ) :
    d ∈ partitionVectorRearrangements lambda ↔
      ∃ e : Equiv.Perm (Fin N), (partitionVectorFinsupp lambda).mapDomain e = d := by
  simp [partitionVectorRearrangements]

/-- The rearrangement orbit is stable under a further permutation of coordinates. -/
theorem mapDomain_mem_partitionVectorRearrangements_iff {N : ℕ}
    (lambda : Nat.PartitionVector N) (e : Equiv.Perm (Fin N)) (d : Fin N →₀ ℕ) :
    d.mapDomain e ∈ partitionVectorRearrangements lambda ↔
      d ∈ partitionVectorRearrangements lambda := by
  constructor
  · intro hd
    rw [mem_partitionVectorRearrangements_iff] at hd ⊢
    obtain ⟨p, hp⟩ := hd
    refine ⟨p.trans e.symm, ?_⟩
    rw [Equiv.coe_trans, Finsupp.mapDomain_comp, hp, ← Finsupp.mapDomain_comp]
    simp
  · intro hd
    rw [mem_partitionVectorRearrangements_iff] at hd ⊢
    obtain ⟨p, hp⟩ := hd
    refine ⟨p.trans e, ?_⟩
    rw [Equiv.coe_trans, Finsupp.mapDomain_comp, hp]

/-- The decreasing representative of a rearrangement orbit is unique. -/
theorem partitionVectorFinsupp_mem_rearrangements_iff {N : ℕ}
    (lambda mu : Nat.PartitionVector N) :
    partitionVectorFinsupp lambda ∈ partitionVectorRearrangements mu ↔ lambda = mu := by
  rw [mem_partitionVectorRearrangements_iff]
  constructor
  · rintro ⟨e, he⟩
    have hfun : (mu : Fin N → ℕ) ∘ e.symm = lambda := by
      funext i
      have h := congrArg (fun d : Fin N →₀ ℕ ↦ d i) he
      simpa [Finsupp.mapDomain_apply_of_injective, partitionVectorFinsupp_apply] using h
    have hanti : Antitone ((mu : Fin N → ℕ) ∘ e.symm) := hfun ▸ lambda.antitone
    have hunique : (mu : Fin N → ℕ) ∘ e.symm = mu :=
      Tuple.unique_antitone (f := (mu : Fin N → ℕ)) (σ := e.symm)
        (τ := Equiv.refl _) hanti (by simpa using mu.antitone)
    apply Nat.PartitionVector.ext
    intro i
    exact congrFun (hfun.symm.trans hunique) i
  · rintro rfl
    exact ⟨Equiv.refl _, by simp [Finsupp.mapDomain_id]⟩

/-- The monomial symmetric polynomial indexed by a fixed-length partition vector. -/
def msymmVec {N : ℕ} (K : Type*) [CommSemiring K]
    (lambda : Nat.PartitionVector N) : MvPolynomial (Fin N) K :=
  ∑ d ∈ partitionVectorRearrangements lambda, monomial d 1

/-- The polynomial `msymmVec` is symmetric. -/
theorem msymmVec_isSymmetric {N : ℕ} (K : Type*) [CommSemiring K]
    (lambda : Nat.PartitionVector N) : (msymmVec K lambda).IsSymmetric := by
  intro e
  simp only [msymmVec, map_sum, rename_monomial]
  exact Finset.sum_equiv (Finsupp.equivCongrLeft e)
    (by
      intro d
      simpa [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain] using
        (mapDomain_mem_partitionVectorRearrangements_iff lambda e d).symm)
    (by
      intro d _
      simp [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain])

/-- The coefficient of a monomial in `msymmVec` is one on the rearrangement orbit and zero
elsewhere. -/
theorem coeff_msymmVec {N : ℕ} (K : Type*) [CommSemiring K]
    (lambda : Nat.PartitionVector N) (d : Fin N →₀ ℕ) :
    (msymmVec K lambda).coeff d =
      if d ∈ partitionVectorRearrangements lambda then 1 else 0 := by
  classical
  simp [msymmVec, coeff_monomial]

/-- At a decreasing exponent vector, the coefficients of the `msymmVec` family are Kronecker
deltas. -/
theorem coeff_msymmVec_partitionVectorFinsupp {N : ℕ} (K : Type*) [CommSemiring K]
    (lambda mu : Nat.PartitionVector N) :
    (msymmVec K mu).coeff (partitionVectorFinsupp lambda) = if lambda = mu then 1 else 0 := by
  rw [coeff_msymmVec]
  simp only [partitionVectorFinsupp_mem_rearrangements_iff]

/-- Every rearrangement of a partition vector has the same total degree. -/
theorem degree_eq_partitionVectorDegree_of_mem {N : ℕ}
    (lambda : Nat.PartitionVector N) {d : Fin N →₀ ℕ}
    (hd : d ∈ partitionVectorRearrangements lambda) :
    d.degree = partitionVectorDegree lambda := by
  rw [mem_partitionVectorRearrangements_iff] at hd
  obtain ⟨e, rfl⟩ := hd
  rw [Finsupp.degree_mapDomain, Finsupp.degree_eq_weight_one]
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, partitionVectorDegree]

/-- A partition-vector monomial symmetric polynomial is homogeneous of the partition size. -/
theorem isHomogeneous_msymmVec {N : ℕ} (K : Type*) [CommSemiring K]
    (lambda : Nat.PartitionVector N) :
    (msymmVec K lambda).IsHomogeneous (partitionVectorDegree lambda) := by
  apply IsHomogeneous.sum
  intro d hd
  exact isHomogeneous_monomial 1 (degree_eq_partitionVectorDegree_of_mem lambda hd)

/-- The partition-vector monomial symmetric polynomials are linearly independent. -/
theorem linearIndependent_msymmVec {N : ℕ} (K : Type*) [Field K] :
    LinearIndependent K (msymmVec K : Nat.PartitionVector N → MvPolynomial (Fin N) K) := by
  rw [linearIndependent_iff']
  intro s g h i hi
  have hc := congrArg (fun p : MvPolynomial (Fin N) K ↦
    p.coeff (partitionVectorFinsupp i)) h
  simp only [coeff_sum, coeff_smul, coeff_msymmVec_partitionVectorFinsupp] at hc
  simpa [hi] using hc

end MvPolynomial
