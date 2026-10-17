/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Coefficients of monomial symmetric polynomials

This file gives a coefficient formula and an orbit-sum expansion for `MvPolynomial.msymm`.

Ported from `RealRooted.Mathlib.RingTheory.MvPolynomial.Symmetric.Monomial` at RealRooted commit
`17a11827921f05b70b269ca8cb3d701d0dee5ba3` (Apache-2.0).
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

open Finset Multiset Sym

variable {R σ : Type*} [CommSemiring R]

/-- The number of variables having a fixed positive exponent in a monomial is the multiplicity
of that exponent in its partition shape. -/
theorem card_filter_count_eq_count_parts [Fintype σ] [DecidableEq σ]
    {n k : ℕ} (s : Sym σ n) (hk : k ≠ 0) :
    #{i : σ | s.1.count i = k} = (Nat.Partition.ofSym s).parts.count k := by
  rw [Nat.Partition.ofSym, Multiset.count_map]
  let t : Finset σ :=
    ⟨s.1.dedup.filter (fun i ↦ k = s.1.count i), s.1.nodup_dedup.filter _⟩
  change #(Finset.univ.filter fun i ↦ s.1.count i = k) = #t
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change s.1.count i = k ↔ i ∈ s.1.dedup.filter (fun i ↦ k = s.1.count i)
  rw [Multiset.mem_filter, Multiset.mem_dedup]
  constructor
  · intro hi
    refine ⟨Multiset.count_pos.mp ?_, hi.symm⟩
    rw [hi]
    exact Nat.zero_lt_of_ne_zero hk
  · exact fun hi ↦ hi.2.symm

/-- Two multisets of variables with the same partition shape differ by a permutation of the
ambient finite type. -/
theorem exists_perm_map_eq_of_ofSym_eq [Finite σ] [DecidableEq σ]
    {n : ℕ} (s t : Sym σ n) (hst : Nat.Partition.ofSym s = Nat.Partition.ofSym t) :
    ∃ e : Equiv.Perm σ, s.map e = t := by
  let _ := Fintype.ofFinite σ
  have hfiber (k : ℕ) :
      Fintype.card {i // s.1.count i = k} = Fintype.card {i // t.1.count i = k} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    by_cases hk : k = 0
    · subst k
      have hspos : #{i : σ | s.1.count i ≠ 0} = s.1.dedup.card := by
        let ssupp : Finset σ := ⟨s.1.dedup, s.1.nodup_dedup⟩
        change #(Finset.univ.filter fun i ↦ s.1.count i ≠ 0) = #ssupp
        apply congrArg Finset.card
        ext i
        simp [ssupp]
      have htpos : #{i : σ | t.1.count i ≠ 0} = t.1.dedup.card := by
        let tsupp : Finset σ := ⟨t.1.dedup, t.1.nodup_dedup⟩
        change #(Finset.univ.filter fun i ↦ t.1.count i ≠ 0) = #tsupp
        apply congrArg Finset.card
        ext i
        simp [tsupp]
      have hcard : s.1.dedup.card = t.1.dedup.card := by
        have h := congrArg (fun p : n.Partition ↦ p.parts.card) hst
        simpa [Nat.Partition.ofSym] using h
      have hssplit := Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (fun i ↦ s.1.count i = 0)
      have htsplit := Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (fun i ↦ t.1.count i = 0)
      change #{i | s.1.count i = 0} + #{i | ¬s.1.count i = 0} = Fintype.card σ at hssplit
      change #{i | t.1.count i = 0} + #{i | ¬t.1.count i = 0} = Fintype.card σ at htsplit
      have hspos' : #{i : σ | ¬s.1.count i = 0} = s.1.dedup.card := by
        simpa only [ne_eq] using hspos
      have htpos' : #{i : σ | ¬t.1.count i = 0} = t.1.dedup.card := by
        simpa only [ne_eq] using htpos
      lia
    · rw [card_filter_count_eq_count_parts s hk,
        card_filter_count_eq_count_parts t hk, hst]
  let fibers (k : ℕ) : {i // s.1.count i = k} ≃ {i // t.1.count i = k} :=
    Fintype.equivOfCardEq (hfiber k)
  let e : Equiv.Perm σ := Equiv.ofFiberEquiv fibers
  refine ⟨e, ?_⟩
  apply Sym.ext
  ext j
  have he := Equiv.ofFiberEquiv_map fibers (e.symm j)
  change t.1.count (e (e.symm j)) = s.1.count (e.symm j) at he
  change (s.1.map e).count j = t.1.count j
  have hc := Multiset.count_map_eq_count' e s.1 e.injective (e.symm j)
  simpa using hc.trans he.symm

/-- A symmetric polynomial has equal coefficients on monomials with the same partition shape. -/
theorem IsSymmetric.coeff_eq_of_ofSym_eq [Finite σ] [DecidableEq σ]
    {P : MvPolynomial σ R} (hP : P.IsSymmetric) {n : ℕ}
    (s t : Sym σ n) (hst : Nat.Partition.ofSym s = Nat.Partition.ofSym t) :
    P.coeff s.1.toFinsupp = P.coeff t.1.toFinsupp := by
  obtain ⟨e, he⟩ := exists_perm_map_eq_of_ofSym_eq s t hst
  have hdomain : s.1.toFinsupp.mapDomain e = t.1.toFinsupp := by
    rw [← he]
    ext i
    rw [Finsupp.mapDomain_equiv_apply, Multiset.toFinsupp_apply,
      Multiset.toFinsupp_apply]
    change s.1.count (e.symm i) = (s.1.map e).count i
    symm
    simpa using Multiset.count_map_eq_count' e s.1 e.injective (e.symm i)
  have hc := coeff_rename_mapDomain e e.injective P s.1.toFinsupp
  rw [hP e, hdomain] at hc
  exact hc.symm

/-- A product of variables indexed by a multiset is the monomial whose exponent vector records
the multiplicities in that multiset. -/
theorem prod_map_X_eq_monomial_toFinsupp [DecidableEq σ] (s : Multiset σ) :
    (s.map (X : σ → MvPolynomial σ R)).prod = monomial s.toFinsupp 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, ih]
      rw [show Multiset.toFinsupp (a ::ₘ s) =
          Finsupp.single a 1 + Multiset.toFinsupp s by
        rw [← Multiset.toFinsupp_singleton, ← Multiset.toFinsupp_add]
        rfl]
      rw [X, monomial_mul_monomial]
      simp only [one_mul]

/-- The coefficient of a monomial in `msymm mu` is one exactly when its exponent multiset has
shape `mu`, and is zero otherwise. -/
theorem coeff_msymm [Nontrivial R] [Fintype σ] [DecidableEq σ]
    {n : ℕ} (mu : n.Partition) (d : σ →₀ ℕ) (hd : d.sum (fun _ k ↦ k) = n) :
    (msymm σ R mu).coeff d =
      if Nat.Partition.ofSym
        (⟨Finsupp.toMultiset d, Finsupp.card_toMultiset d |>.trans hd⟩ : Sym σ n) = mu
      then 1 else 0 := by
  let s : Sym σ n :=
    ⟨Finsupp.toMultiset d, Finsupp.card_toMultiset d |>.trans hd⟩
  change (msymm σ R mu).coeff d = if Nat.Partition.ofSym s = mu then 1 else 0
  rw [msymm, coeff_sum]
  simp_rw [prod_map_X_eq_monomial_toFinsupp, coeff_monomial]
  by_cases hs : Nat.Partition.ofSym s = mu
  · simp only [hs, reduceIte]
    let smu : {a : Sym σ n // Nat.Partition.ofSym a = mu} := ⟨s, hs⟩
    rw [Fintype.sum_eq_single smu]
    · simp [smu, s]
    · intro t hts
      simp only [ite_eq_right_iff]
      intro heq
      have ht : t = smu := by
        apply Subtype.ext
        apply Sym.ext
        simpa [smu, s] using Multiset.toFinsupp_eq_iff.mp heq
      exact (hts ht).elim
  · simp only [hs, reduceIte]
    apply Finset.sum_eq_zero
    intro t _
    simp only [ite_eq_right_iff]
    intro heq
    have ht : (t : Sym σ n) = s := by
      apply Sym.ext
      simpa [s] using Multiset.toFinsupp_eq_iff.mp heq
    have hshape : Nat.Partition.ofSym s = mu := by
      rw [← ht]
      exact t.2
    exact (hs hshape).elim

/-- A monomial symmetric polynomial is homogeneous of the size of its indexing partition. -/
theorem isHomogeneous_msymm [Fintype σ] [DecidableEq σ]
    {n : ℕ} (mu : n.Partition) : IsHomogeneous (msymm σ R mu) n := by
  rw [msymm]
  apply IsHomogeneous.sum
  intro s _
  rw [prod_map_X_eq_monomial_toFinsupp]
  apply isHomogeneous_monomial
  exact (Multiset.toFinsupp_sum_eq s.1.1).trans s.1.2

/-- The coefficient of a symmetric polynomial on a monomial-symmetric orbit. It is zero when
that orbit is empty in the ambient variable type. -/
def msymmCoeff [Fintype σ] [DecidableEq σ] {n : ℕ}
    (P : MvPolynomial σ R) (mu : n.Partition) : R := by
  classical
  exact if h : Nonempty {s : Sym σ n // Nat.Partition.ofSym s = mu} then
      P.coeff (Classical.choice h).1.1.toFinsupp
    else 0

/-- The orbit coefficient at the shape of an existing monomial is its ordinary coefficient. -/
theorem msymmCoeff_eq_coeff [Fintype σ] [DecidableEq σ]
    {P : MvPolynomial σ R} (hP : P.IsSymmetric) {n : ℕ} (s : Sym σ n) :
    msymmCoeff P (Nat.Partition.ofSym s) = P.coeff s.1.toFinsupp := by
  rw [msymmCoeff]
  split
  case isTrue h =>
    exact hP.coeff_eq_of_ofSym_eq (Classical.choice h).1 s (Classical.choice h).2
  case isFalse h => exact (h ⟨s, rfl⟩).elim

/-- Every symmetric homogeneous polynomial is the sum of its monomial-symmetric orbit
components. -/
theorem eq_sum_msymm [Nontrivial R] [Fintype σ] [DecidableEq σ]
    {P : MvPolynomial σ R} {n : ℕ} (hP : P.IsSymmetric) (hhom : P.IsHomogeneous n) :
    P = ∑ mu : n.Partition, msymmCoeff P mu • msymm σ R mu := by
  ext d
  by_cases hd : d.sum (fun _ k ↦ k) = n
  · rw [coeff_sum]
    simp_rw [coeff_smul, coeff_msymm (R := R) _ d hd]
    let s : Sym σ n :=
      ⟨Finsupp.toMultiset d, Finsupp.card_toMultiset d |>.trans hd⟩
    change P.coeff d = ∑ mu : n.Partition,
      msymmCoeff P mu * if Nat.Partition.ofSym s = mu then 1 else 0
    rw [show (∑ mu : n.Partition,
        msymmCoeff P mu * if Nat.Partition.ofSym s = mu then 1 else 0) =
        msymmCoeff P (Nat.Partition.ofSym s) by
      classical
      simp]
    rw [msymmCoeff_eq_coeff hP s]
    rw [Finsupp.toMultiset_toFinsupp]
  · have hzeroP : P.coeff d = 0 := by
      by_contra hcoeff
      apply hd
      have hdegree := hhom hcoeff
      have hdegree' : d.degree = n := by
        rw [Finsupp.degree_eq_weight_one]
        exact hdegree
      exact hdegree'
    rw [hzeroP, coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro mu _
    rw [coeff_smul]
    have hzero : (msymm σ R mu).coeff d = 0 := by
      by_contra hcoeff
      apply hd
      have hdegree := isHomogeneous_msymm (R := R) mu hcoeff
      have hdegree' : d.degree = n := by
        rw [Finsupp.degree_eq_weight_one]
        exact hdegree
      exact hdegree'
    rw [hzero, smul_eq_mul, mul_zero]

end MvPolynomial
