/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Homogeneous expansions in elementary symmetric polynomials

This file refines the fundamental theorem of symmetric polynomials by degree. It gives existence
of an elementary expansion for a homogeneous symmetric polynomial, proves uniqueness in at least
as many variables as the degree, and uses uniqueness to descend nonnegative rational coefficients
of an integral polynomial to natural-number coefficients.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace MvPolynomial

variable {σ R S : Type*} [Fintype σ]

/-- An elementary symmetric polynomial is homogeneous of its index. -/
theorem isHomogeneous_esymm [CommSemiring R] (m : ℕ) :
    (esymm σ R m).IsHomogeneous m := by
  classical
  rw [esymm]
  apply IsHomogeneous.sum
  intro t ht
  rw [Finset.mem_powersetCard] at ht
  convert IsHomogeneous.prod t (fun i ↦ X i) (fun _ ↦ 1)
    (fun i _ ↦ isHomogeneous_X R i) using 1
  simpa using ht.2.symm

/-- Changing coefficients commutes with elementary symmetric polynomials indexed by a partition. -/
theorem map_esymmPart [CommSemiring R] [CommSemiring S] {n : ℕ} (ν : n.Partition)
    (g : R →+* S) :
    map g (esymmPart σ R ν) = esymmPart σ S ν := by
  simp only [esymmPart, map_multiset_prod, Multiset.map_map, Function.comp_apply]
  simp_rw [map_esymm σ R]

private theorem sum_map_toMultiset {α : Type*} (d : α →₀ ℕ) (g : α → ℕ) :
    (d.toMultiset.map g).sum = d.sum fun i k ↦ k * g i := by
  classical
  induction d using Finsupp.induction with
  | zero => simp
  | single_add a b d ha hb ih =>
      rw [Finsupp.toMultiset_add, Finsupp.toMultiset_single, Multiset.map_add,
        Multiset.sum_add]
      rw [Finsupp.sum_add_index (by simp) (by simp [add_mul])]
      rw [Multiset.map_nsmul, Multiset.sum_nsmul]
      simp [ih]

private theorem prod_map_toMultiset {α M : Type*} [CommMonoid M]
    (d : α →₀ ℕ) (g : α → M) :
    (d.toMultiset.map g).prod = d.prod fun i k ↦ g i ^ k := by
  classical
  induction d using Finsupp.induction with
  | zero => simp
  | single_add a b d ha hb ih =>
      rw [Finsupp.toMultiset_add, Finsupp.toMultiset_single, Multiset.map_add,
        Multiset.prod_add]
      rw [Finsupp.prod_add_index (by simp) (by simp [pow_add])]
      rw [Multiset.map_nsmul, Multiset.prod_nsmul]
      simp [ih]

private def finsuppPartition {N n : ℕ} (d : Fin N →₀ ℕ)
    (hd : Finsupp.weight (fun i : Fin N ↦ i.val + 1) d = n) : n.Partition where
  parts := d.toMultiset.map fun i ↦ i.val + 1
  parts_pos := by simp
  parts_sum := by
    rw [sum_map_toMultiset]
    simpa [Finsupp.weight_apply, mul_comm] using hd

private theorem finsuppPartition_parts_le {N n : ℕ} (d : Fin N →₀ ℕ)
    (hd : Finsupp.weight (fun i : Fin N ↦ i.val + 1) d = n) :
    ∀ m ∈ (finsuppPartition d hd).parts, m ≤ N := by
  simp only [finsuppPartition, Multiset.mem_map]
  rintro m ⟨i, -, rfl⟩
  exact i.isLt

private theorem esymmAlgHomMonomial_eq_smul_esymmPart [CommSemiring R]
    {N n : ℕ} (d : Fin N →₀ ℕ) (r : R)
    (hd : Finsupp.weight (fun i : Fin N ↦ i.val + 1) d = n) :
    esymmAlgHomMonomial (Fin N) d r = r • esymmPart (Fin N) R (finsuppPartition d hd) := by
  rw [esymmAlgHomMonomial, esymmAlgHom_apply, aeval_monomial]
  simp only [esymmPart, finsuppPartition, Multiset.map_map, Function.comp_apply,
    Algebra.smul_def, algebraMap_eq]
  rw [prod_map_toMultiset]

private theorem isHomogeneous_esymmAlgHomMonomial [CommSemiring R]
    {N : ℕ} (d : Fin N →₀ ℕ) (r : R) :
    (esymmAlgHomMonomial (Fin N) d r).IsHomogeneous
      (Finsupp.weight (fun i : Fin N ↦ i.val + 1) d) := by
  rw [esymmAlgHomMonomial, esymmAlgHom_apply, aeval_monomial]
  rw [algebraMap_eq]
  have hprod :
      (∏ i ∈ d.support, esymm (Fin N) R (i.val + 1) ^ d i).IsHomogeneous
        (∑ i ∈ d.support, (i.val + 1) * d i) :=
    IsHomogeneous.prod d.support
    (fun i ↦ esymm (Fin N) R (i.val + 1) ^ d i)
    (fun i ↦ (i.val + 1) * d i)
    (fun i _ ↦ (isHomogeneous_esymm (σ := Fin N) (R := R) (i.val + 1)).pow (d i))
  rw [Finsupp.prod]
  convert (isHomogeneous_C (Fin N) r).mul hprod using 1
  rw [zero_add, Finsupp.weight_apply, Finsupp.sum]
  simp only [nsmul_eq_mul, Nat.cast_id, mul_comm]

private theorem homogeneousComponent_esymmAlgHom [CommSemiring R] {N : ℕ}
    (q : MvPolynomial (Fin N) R) (n : ℕ) :
    homogeneousComponent n (esymmAlgHom (Fin N) R N q).val =
      (esymmAlgHom (Fin N) R N
        (weightedHomogeneousComponent (fun i : Fin N ↦ i.val + 1) n q)).val := by
  induction q using MvPolynomial.induction_on' with
  | monomial d r =>
      have hhom := isHomogeneous_esymmAlgHomMonomial (R := R) d r
      rw [weightedHomogeneousComponent_of_mem
        (isWeightedHomogeneous_monomial _ d r rfl)]
      change homogeneousComponent n (esymmAlgHomMonomial (Fin N) d r) = _
      rw [homogeneousComponent_of_mem hhom]
      split_ifs <;> simp [esymmAlgHomMonomial]
  | add p q hp hq => simp [map_add, hp, hq]

private theorem exists_elementaryExpansion_of_isWeightedHomogeneous [CommRing R]
    {N n : ℕ} {q : MvPolynomial (Fin N) R}
    (hq : q.IsWeightedHomogeneous (fun i : Fin N ↦ i.val + 1) n) :
    ∃ c : n.Partition → R,
      (∀ ν, (∃ m ∈ ν.parts, N < m) → c ν = 0) ∧
      (esymmAlgHom (Fin N) R N q).val =
        ∑ ν : n.Partition, c ν • esymmPart (Fin N) R ν := by
  induction hq using IsWeightedHomogeneous.induction_on with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · simp
      · simp
  | add p q hp hq ihp ihq =>
      obtain ⟨c, hc, hp'⟩ := ihp
      obtain ⟨b, hb, hq'⟩ := ihq
      refine ⟨c + b, ?_, ?_⟩
      · intro ν hν
        simp [hc ν hν, hb ν hν]
      · rw [map_add]
        change (esymmAlgHom (Fin N) R N p).val +
            (esymmAlgHom (Fin N) R N q).val = _
        rw [hp', hq']
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  | monomial d r hd =>
      let ν := finsuppPartition d hd
      refine ⟨fun μ ↦ if μ = ν then r else 0, ?_, ?_⟩
      · intro μ hμ
        apply ite_eq_right
        rintro rfl
        obtain ⟨m, hm, hmN⟩ := hμ
        exact hmN.not_ge (finsuppPartition_parts_le d hd m hm)
      · rw [show (esymmAlgHom (Fin N) R N (monomial d r)).val =
          esymmAlgHomMonomial (Fin N) d r by rfl]
        rw [esymmAlgHomMonomial_eq_smul_esymmPart d r hd]
        simp [ν]

/-- A homogeneous symmetric polynomial is a linear combination of elementary symmetric
polynomials indexed by partitions of its degree. Coefficients outside the partitions whose parts
are at most the number of variables vanish. -/
theorem IsSymmetric.exists_eq_sum_smul_esymmPart [CommRing R] {N n : ℕ}
    {f : MvPolynomial (Fin N) R} (hsym : f.IsSymmetric) (hhom : f.IsHomogeneous n) :
    ∃ c : n.Partition → R,
      (∀ ν, (∃ m ∈ ν.parts, N < m) → c ν = 0) ∧
      f = ∑ ν : n.Partition, c ν • esymmPart (Fin N) R ν := by
  let sf : symmetricSubalgebra (Fin N) R := ⟨f, hsym⟩
  let q := (esymmAlgEquiv (n := N) (Fin N) R (by simp)).symm sf
  let qn := weightedHomogeneousComponent (fun i : Fin N ↦ i.val + 1) n q
  obtain ⟨c, hc, heq⟩ := exists_elementaryExpansion_of_isWeightedHomogeneous
    (weightedHomogeneousComponent_isWeightedHomogeneous n q)
  refine ⟨c, hc, ?_⟩
  rw [← heq, ← homogeneousComponent_esymmAlgHom q n]
  have hq : (esymmAlgHom (Fin N) R N q).val = f := by
    change ((esymmAlgEquiv (n := N) (Fin N) R (by simp)) q).val = f
    simp [q, sf]
  rw [hq]
  exact (homogeneousComponent_eq_self hhom).symm

private theorem partition_part_bounds {N n : ℕ} (hn : n ≤ N) (ν : n.Partition) :
    ∀ m ∈ ν.parts, 0 < m ∧ m ≤ N := by
  intro m hm
  exact ⟨ν.parts_pos hm, (ν.le_of_mem_parts hm).trans hn⟩

private def partitionFinMultiset {N n : ℕ} (hn : n ≤ N) (ν : n.Partition) :
    Multiset (Fin N) :=
  ν.parts.pmap (fun m hm ↦ ⟨m - 1, by lia⟩) (partition_part_bounds hn ν)

private theorem map_partitionFinMultiset {N n : ℕ} (hn : n ≤ N) (ν : n.Partition) :
    (partitionFinMultiset hn ν).map (fun i ↦ i.val + 1) = ν.parts := by
  rw [partitionFinMultiset, Multiset.map_pmap]
  calc
    _ = ν.parts.pmap (fun m _ ↦ m) (partition_part_bounds hn ν) := by
      apply Multiset.pmap_congr
      intro m hm h₁ h₂
      dsimp
      have := (partition_part_bounds hn ν m hm).1
      lia
    _ = ν.parts.map id := Multiset.pmap_eq_map _ _ _ _
    _ = ν.parts := Multiset.map_id _

private def partitionExponent {N n : ℕ} (hn : n ≤ N) (ν : n.Partition) : Fin N →₀ ℕ :=
  Multiset.toFinsupp (partitionFinMultiset hn ν)

private theorem map_toMultiset_partitionExponent {N n : ℕ} (hn : n ≤ N)
    (ν : n.Partition) :
    (partitionExponent hn ν).toMultiset.map (fun i ↦ i.val + 1) = ν.parts := by
  simp [partitionExponent, map_partitionFinMultiset]

private theorem partitionExponent_injective {N n : ℕ} (hn : n ≤ N) :
    Function.Injective (partitionExponent hn) := by
  intro ν μ h
  apply Nat.Partition.ext
  rw [← map_toMultiset_partitionExponent hn ν,
    ← map_toMultiset_partitionExponent hn μ, h]

private theorem esymmAlgHomMonomial_partitionExponent [CommSemiring R]
    {N n : ℕ} (hn : n ≤ N) (ν : n.Partition) (r : R) :
    esymmAlgHomMonomial (Fin N) (partitionExponent hn ν) r =
      r • esymmPart (Fin N) R ν := by
  rw [esymmAlgHomMonomial, esymmAlgHom_apply, aeval_monomial]
  simp only [esymmPart, Algebra.smul_def, algebraMap_eq]
  rw [← prod_map_toMultiset]
  rw [← map_toMultiset_partitionExponent hn ν]
  simp only [Multiset.map_map, Function.comp_apply]

/-- In at least as many variables as the degree, the elementary symmetric polynomials indexed by
partitions of that degree are linearly independent. -/
theorem linearIndependent_esymmPart [CommRing R] {N n : ℕ} (hn : n ≤ N) :
    LinearIndependent R (fun ν : n.Partition ↦ esymmPart (Fin N) R ν) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc ν
  have hsum : ∑ μ : n.Partition, monomial (partitionExponent hn μ) (c μ) = 0 := by
    apply esymmAlgHom_fin_injective R le_rfl
    rw [map_sum, map_zero]
    apply Subtype.ext
    change (Subalgebra.val (symmetricSubalgebra (Fin N) R))
        (∑ μ : n.Partition,
          esymmAlgHom (Fin N) R N (monomial (partitionExponent hn μ) (c μ))) =
      (Subalgebra.val (symmetricSubalgebra (Fin N) R)) 0
    rw [map_sum, map_zero]
    change ∑ μ : n.Partition,
        esymmAlgHomMonomial (Fin N) (partitionExponent hn μ) (c μ) = 0
    simpa only [esymmAlgHomMonomial_partitionExponent] using hc
  have hcoeff := congrArg
    (fun p : MvPolynomial (Fin N) R ↦ p.coeff (partitionExponent hn ν)) hsum
  simpa [coeff_monomial, (partitionExponent_injective hn).eq_iff] using hcoeff

/-- Elementary-expansion coefficients commute with a change of coefficient ring whenever the
elementary expansion is unique. -/
theorem elementaryExpansion_coeff_map [CommRing R] [CommRing S] {N n : ℕ} (hn : n ≤ N)
    (g : R →+* S) (f : MvPolynomial (Fin N) R) (c : n.Partition → R)
    (b : n.Partition → S)
    (hc : f = ∑ ν : n.Partition, c ν • esymmPart (Fin N) R ν)
    (hb : map g f = ∑ ν : n.Partition, b ν • esymmPart (Fin N) S ν) :
    ∀ ν, g (c ν) = b ν := by
  have heq :
      (∑ ν : n.Partition, g (c ν) • esymmPart (Fin N) S ν) =
        ∑ ν : n.Partition, b ν • esymmPart (Fin N) S ν := by
    rw [← hb, hc, map_sum]
    simp_rw [smul_eq_C_mul, map_mul, map_C, map_esymmPart]
  have hzero :
      ∑ ν : n.Partition, (g (c ν) - b ν) • esymmPart (Fin N) S ν = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, heq, sub_self]
  intro ν
  exact sub_eq_zero.mp
    (Fintype.linearIndependent_iff.mp (linearIndependent_esymmPart (R := S) hn)
      (fun μ ↦ g (c μ) - b μ) hzero ν)

/-- If an integral homogeneous symmetric polynomial has a nonnegative rational elementary
expansion in at least as many variables as its degree, then it has an expansion with
natural-number coefficients over the integers. -/
theorem IsSymmetric.exists_eq_sum_nsmul_esymmPart_of_map_nonneg
    {N n : ℕ} {f : MvPolynomial (Fin N) ℤ} (hsym : f.IsSymmetric)
    (hhom : f.IsHomogeneous n) (hn : n ≤ N)
    (hq : ∃ c : n.Partition → ℚ,
      (∀ ν, 0 ≤ c ν) ∧
      MvPolynomial.map (Int.castRingHom ℚ) f =
        ∑ ν : n.Partition, c ν • esymmPart (Fin N) ℚ ν) :
    ∃ c : n.Partition → ℕ,
      f = ∑ ν : n.Partition, c ν • esymmPart (Fin N) ℤ ν := by
  obtain ⟨cℤ, -, hcℤ⟩ := hsym.exists_eq_sum_smul_esymmPart hhom
  obtain ⟨cℚ, hcℚ, heqℚ⟩ := hq
  have hcast := elementaryExpansion_coeff_map hn (Int.castRingHom ℚ) f cℤ cℚ hcℤ heqℚ
  have hcℤ_nonneg : ∀ ν, 0 ≤ cℤ ν := by
    intro ν
    have hnonneg : (0 : ℚ) ≤ (cℤ ν : ℚ) := by
      change 0 ≤ (Int.castRingHom ℚ) (cℤ ν)
      rw [hcast ν]
      exact hcℚ ν
    exact Int.cast_nonneg_iff.mp hnonneg
  refine ⟨fun ν ↦ (cℤ ν).toNat, ?_⟩
  rw [hcℤ]
  apply Finset.sum_congr rfl
  intro ν _
  have hcoeff : cℤ ν = ((cℤ ν).toNat : ℤ) :=
    (Int.toNat_of_nonneg (hcℤ_nonneg ν)).symm
  rw [hcoeff, natCast_zsmul]

end MvPolynomial
