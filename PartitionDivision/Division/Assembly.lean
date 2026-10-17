/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Division.TraceIdentity
public import PartitionDivision.Mathlib.Algebra.MvPolynomial.NonnegCoeffs
public import PartitionDivision.Mathlib.RingTheory.MvPolynomial.Symmetric.ElementaryExpansion

/-!
# Assembly of the conditional partition-division expansion

This file transfers the abstract trace identity through the coefficient rings used at
specialization, extracts a nonnegative elementary expansion over the rationals, and descends it
to a natural-number expansion over the integers.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace PartitionDivision

open Matrix MvPolynomial

private theorem map_aeval_expanded_esymm
    {R S : Type*} [CommSemiring R] [CommSemiring S] (g : R →+* S)
    {N k : ℕ} (p : MvPolynomial (Fin N) R) :
    map g (aeval (fun i : Fin N ↦ expand k (esymm (Fin N) R (i + 1))) p) =
      aeval (fun i : Fin N ↦ expand k (esymm (Fin N) S (i + 1))) (map g p) := by
  rw [map_aeval, aeval_eq_eval₂Hom, eval₂Hom_map_hom]
  apply congrArg (fun φ : MvPolynomial (Fin N) R →+* MvPolynomial (Fin N) S ↦ φ p)
  ext i <;> simp [map_esymm]

private theorem map_trace_list_prod
    {R S ι : Type*} [CommSemiring R] [CommSemiring S]
    [Fintype ι] [DecidableEq ι] (g : R →+* S) (l : List (Matrix ι ι R)) :
    g (trace l.prod) = trace (l.map fun A ↦ A.map g).prod := by
  rw [AddMonoidHom.map_trace]
  congr 1
  induction l with
  | nil => simp
  | cons A l ih => simp [List.prod_cons, Matrix.map_mul, ih]

private theorem map_specializedTrace
    {R S ι : Type*} [CommSemiring R] [CommSemiring S]
    [Fintype ι] [DecidableEq ι] (g : R →+* S) {N k : ℕ}
    (M : ℕ → Matrix ι ι (MvPolynomial (Fin N) R)) (l : List ℕ) :
    map g (trace ((l.map fun r ↦ (M r).map
      (aeval fun i : Fin N ↦ expand k (esymm (Fin N) R (i + 1)))).reverse.prod)) =
      trace ((l.map fun r ↦ ((M r).map (map g)).map
        (aeval fun i : Fin N ↦ expand k (esymm (Fin N) S (i + 1)))).reverse.prod) := by
  rw [map_trace_list_prod]
  congr 1
  simp only [List.map_reverse, List.map_map]
  apply congrArg List.prod
  apply congrArg List.reverse
  apply List.map_congr_left
  intro r _
  apply Matrix.ext
  intro i j
  exact map_aeval_expanded_esymm g (M r i j)

private theorem map_exponentFilter
    {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (g : R →+* S) (k : ℕ) (f : MvPolynomial σ R) :
    map g (exponentFilter k f) = exponentFilter k (map g f) := by
  rw [exponentFilter_eq_expand_exponentDiv, map_expand, map_exponentDiv,
    ← exponentFilter_eq_expand_exponentDiv]

private theorem map_list_prod_esymm
    {R S : Type*} [CommSemiring R] [CommSemiring S] (g : R →+* S)
    {N : ℕ} (l : List ℕ) :
    map g ((l.map fun r ↦ esymm (Fin N) R r).prod) =
      (l.map fun r ↦ esymm (Fin N) S r).prod := by
  induction l with
  | nil => simp
  | cons r l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [map_mul, map_esymm, ih]

private theorem map_natCast_pow_smul
    {R S σ : Type*} [CommSemiring R] [CommSemiring S] (g : R →+* S)
    (q N : ℕ) (f : MvPolynomial σ R) :
    map g ((q : R) ^ N • f) = (q : S) ^ N • map g f := by
  simp [smul_eq_C_mul]

/-- Stage (a): an abstract trace identity descends through an injective coefficient extension,
specializes, and then descends from a characteristic-zero field to the rationals. -/
theorem trace_identity_over_rat_of_base_change
    {A F G ι : Type*} [CommRing A] [Algebra ℚ A]
    [Field F] [Algebra A F] [Field G] [CharZero G] [Algebra ℚ G]
    [Fintype ι] [DecidableEq ι] {N k : ℕ}
    (hAF : Function.Injective (algebraMap A F)) (ev : A →ₐ[ℚ] G)
    (M : ℕ → Matrix ι ι (MvPolynomial (Fin N) F))
    (MA : ℕ → Matrix ι ι (MvPolynomial (Fin N) A))
    (M0 : ℕ → Matrix ι ι (MvPolynomial (Fin N) ℚ))
    (hMAF : ∀ r, M r = (MA r).map (map (algebraMap A F)))
    (hMAG : ∀ r, (MA r).map (MvPolynomial.map ev.toRingHom) =
      (M0 r).map (MvPolynomial.map (algebraMap ℚ G))) (l : List ℕ)
    (hF : trace ((l.map fun r ↦ (M r).map
      (aeval fun i : Fin N ↦ expand k (esymm (Fin N) F (i + 1)))).reverse.prod) =
      (k ^ N : F) • exponentFilter k
        ((l.map fun r ↦ esymm (Fin N) F r).prod)) :
    trace ((l.map fun r ↦ (M0 r).map
      (aeval fun i : Fin N ↦ expand k (esymm (Fin N) ℚ (i + 1)))).reverse.prod) =
      (k ^ N : ℚ) • exponentFilter k
        ((l.map fun r ↦ esymm (Fin N) ℚ r).prod) := by
  classical
  have hA : trace ((l.map fun r ↦ (MA r).map
      (aeval fun i : Fin N ↦ expand k (esymm (Fin N) A (i + 1)))).reverse.prod) =
      (k ^ N : A) • exponentFilter k
        ((l.map fun r ↦ esymm (Fin N) A r).prod) := by
    apply MvPolynomial.map_injective (algebraMap A F) hAF
    rw [map_specializedTrace]
    simp only [← hMAF]
    rw [map_natCast_pow_smul, map_exponentFilter, map_list_prod_esymm]
    exact hF
  have hG : trace ((l.map fun r ↦ ((M0 r).map (map (algebraMap ℚ G))).map
      (aeval fun i : Fin N ↦ expand k (esymm (Fin N) G (i + 1)))).reverse.prod) =
      (k ^ N : G) • exponentFilter k
        ((l.map fun r ↦ esymm (Fin N) G r).prod) := by
    have := congrArg (MvPolynomial.map ev.toRingHom) hA
    rw [map_specializedTrace, map_natCast_pow_smul, map_exponentFilter,
      map_list_prod_esymm] at this
    simpa only [hMAG] using this
  apply MvPolynomial.map_injective (algebraMap ℚ G) (algebraMap ℚ G).injective
  rw [map_specializedTrace, map_natCast_pow_smul, map_exponentFilter,
    map_list_prod_esymm]
  exact hG

/-- Stage (b): the trace of a product of entrywise nonnegative transition matrices is
coefficientwise nonnegative, and its elementary specialization is the specialized trace. -/
theorem trace_list_prod_hasNonnegCoeffs_and_aeval_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {N k : ℕ}
    (M0 : ℕ → Matrix ι ι (MvPolynomial (Fin N) ℚ))
    (hM0 : ∀ r i j, (M0 r i j).HasNonnegCoeffs) (l : List ℕ)
    {f : MvPolynomial (Fin N) ℚ}
    (htrace : trace ((l.map fun r ↦ (M0 r).map
      (aeval fun i : Fin N ↦ expand k (esymm (Fin N) ℚ (i + 1)))).reverse.prod) =
      f) :
    let T := trace (l.map M0).reverse.prod
    T.HasNonnegCoeffs ∧
      aeval (fun i : Fin N ↦ expand k (esymm (Fin N) ℚ (i + 1))) T = f := by
  classical
  dsimp only
  constructor
  · apply Matrix.hasNonnegCoeffs_trace_list_prod
    intro A hA i j
    simp only [List.mem_reverse, List.mem_map] at hA
    obtain ⟨r, -, rfl⟩ := hA
    exact hM0 r i j
  · calc
      _ = trace ((l.map M0).reverse.map fun A ↦ A.map
          (aeval fun i : Fin N ↦ expand k (esymm (Fin N) ℚ (i + 1)))).prod :=
        map_trace_list_prod
          (aeval fun i : Fin N ↦ expand k (esymm (Fin N) ℚ (i + 1))).toRingHom _
      _ = f := by
        have hl :
            l.map ((fun A ↦ A.map
              (aeval fun i : Fin N ↦ expand k (esymm (Fin N) ℚ (i + 1)))) ∘ M0) =
              l.map fun r ↦ (M0 r).map
                (aeval fun i : Fin N ↦ expand k (esymm (Fin N) ℚ (i + 1))) := by
          apply List.map_congr_left
          intro r _
          rfl
        rw [List.map_reverse, List.map_map, hl]
        exact htrace

/-- Stage (c): injectivity of exponent expansion removes `expand` from the specialized trace
identity and turns the exponent filter into exponent division. -/
theorem aeval_esymm_eq_smul_exponentDiv_of_aeval_expand_eq
    {N k q : ℕ} (hk : 0 < k) {T f : MvPolynomial (Fin N) ℚ}
    (h : aeval (fun i : Fin N ↦ expand k (esymm (Fin N) ℚ (i + 1))) T =
      (q : ℚ) • exponentFilter k f) :
    aeval (fun i : Fin N ↦ esymm (Fin N) ℚ (i + 1)) T =
      (q : ℚ) • exponentDiv k f := by
  apply expand_injective hk
  rw [comp_aeval_apply, h, map_smul, exponentFilter_eq_expand_exponentDiv]

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

private theorem aeval_esymm_monomial_partitionExponent
    {R : Type*} [CommSemiring R] {N n : ℕ} (hn : n ≤ N) (ν : n.Partition) (r : R) :
    aeval (fun i : Fin N ↦ esymm (Fin N) R (i + 1))
        (monomial (partitionExponent hn ν) r) =
      r • esymmPart (Fin N) R ν := by
  rw [aeval_monomial]
  simp only [esymmPart, Algebra.smul_def, algebraMap_eq]
  rw [← prod_map_toMultiset]
  rw [← map_toMultiset_partitionExponent hn ν]
  simp only [Multiset.map_map, Function.comp_apply]

/-- Stage (d): positivity of a polynomial in the elementary generators gives a nonnegative
elementary expansion after division by the positive trace scalar. -/
theorem exists_nonneg_esymm_expansion_of_aeval_eq_smul
    {N n q : ℕ} (hq : 0 < q) (hn : n ≤ N)
    {T f : MvPolynomial (Fin N) ℚ} (hT : T.HasNonnegCoeffs)
    (hsym : f.IsSymmetric) (hhom : f.IsHomogeneous n)
    (heq : aeval (fun i : Fin N ↦ esymm (Fin N) ℚ (i + 1)) T =
      (q : ℚ) • f) :
    ∃ c : n.Partition → ℚ,
      (∀ ν, 0 ≤ c ν) ∧ f = ∑ ν, c ν • esymmPart (Fin N) ℚ ν := by
  classical
  obtain ⟨c, -, hc⟩ := hsym.exists_eq_sum_smul_esymmPart hhom
  let Q : MvPolynomial (Fin N) ℚ :=
    ∑ ν : n.Partition, monomial (partitionExponent hn ν) (c ν)
  have hQ : aeval (fun i : Fin N ↦ esymm (Fin N) ℚ (i + 1)) Q = f := by
    simp only [Q, map_sum, hc]
    apply Finset.sum_congr rfl
    intro ν _
    exact aeval_esymm_monomial_partitionExponent hn ν (c ν)
  have hTQ : T = (q : ℚ) • Q := by
    apply esymmAlgHom_fin_injective ℚ le_rfl
    apply Subtype.ext
    simp only [esymmAlgHom_apply]
    rw [heq, map_smul, hQ]
  refine ⟨c, ?_, hc⟩
  intro ν
  have hcoeff := hT (partitionExponent hn ν)
  rw [hTQ, coeff_smul, coeff_sum] at hcoeff
  simp only [coeff_monomial, (partitionExponent_injective hn).eq_iff,
    Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left] at hcoeff
  have hqℚ : (0 : ℚ) < q := by exact_mod_cast hq
  exact nonneg_of_mul_nonneg_right (by simpa only [smul_eq_mul] using hcoeff) hqℚ

/-- Stage (e): a nonnegative rational elementary expansion of the mapped exponent quotient
descends to a natural-number elementary expansion over the integers. -/
theorem exists_nat_esymm_expansion_of_map_exponentDiv_nonneg
    {N n k : ℕ} (hk : 0 < k) (hn : n ≤ N) (μ : (k * n).Partition)
    (hsym : (esymmPart (Fin N) ℤ μ).IsSymmetric)
    (hhom : (esymmPart (Fin N) ℤ μ).IsHomogeneous (k * n))
    (hq : ∃ c : n.Partition → ℚ,
      (∀ ν, 0 ≤ c ν) ∧
      exponentDiv k (esymmPart (Fin N) ℚ μ) =
        ∑ ν, c ν • esymmPart (Fin N) ℚ ν) :
    ∃ c : n.Partition → ℕ,
      exponentDiv k (esymmPart (Fin N) ℤ μ) =
        ∑ ν, c ν • esymmPart (Fin N) ℤ ν := by
  apply (hsym.exponentDiv k).exists_eq_sum_nsmul_esymmPart_of_map_nonneg
    (hhom.exponentDiv hk) hn
  obtain ⟨c, hc, heq⟩ := hq
  refine ⟨c, hc, ?_⟩
  rw [map_exponentDiv, map_esymmPart]
  exact heq

private theorem isSymmetric_esymmPart
    {R : Type*} [CommSemiring R] {N m : ℕ} (μ : m.Partition) :
    (esymmPart (Fin N) R μ).IsSymmetric := by
  classical
  rw [esymmPart]
  induction μ.parts using Multiset.induction_on with
  | empty => exact IsSymmetric.one
  | cons r s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      exact (esymm_isSymmetric (Fin N) R r).mul ih

private theorem isHomogeneous_esymmPart
    {R : Type*} [CommSemiring R] {N m : ℕ} (μ : m.Partition) :
    (esymmPart (Fin N) R μ).IsHomogeneous m := by
  classical
  have h (s : Multiset ℕ) :
      ((s.map fun r ↦ esymm (Fin N) R r).prod).IsHomogeneous s.sum := by
    induction s using Multiset.induction_on with
    | empty => simpa using isHomogeneous_one (σ := Fin N) R
    | cons r s ih =>
        simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
        exact (isHomogeneous_esymm (σ := Fin N) (R := R) r).mul ih
  rw [esymmPart]
  simpa only [μ.parts_sum] using h μ.parts

private theorem list_prod_esymm_parts_toList
    {R : Type*} [CommSemiring R] {N m : ℕ} (μ : m.Partition) :
    (μ.parts.toList.map fun r ↦ esymm (Fin N) R r).prod =
      esymmPart (Fin N) R μ := by
  rw [esymmPart]
  simp

/-- The conditional end-to-end assembly: positive rational transition matrices satisfying the
abstract trace identity yield a natural-number elementary expansion of the exponent quotient. -/
theorem exists_nat_esymm_expansion_of_transition_matrices
    {A F G ι : Type*} [CommRing A] [Algebra ℚ A]
    [Field F] [CharZero F] [Algebra A F]
    [Field G] [CharZero G] [Algebra ℚ G]
    {N k n : ℕ} (hk : 0 < k) (hn : n ≤ N) (μ : (k * n).Partition)
    {ζ : F} (hζ : IsPrimitiveRoot ζ k) [Fintype ι]
    (hcard : Fintype.card ι = k ^ N) (o : ι) (B : ι → MvPolynomial (Fin N) F)
    (hBo : B o = 1) (M : ℕ → Matrix ι ι (MvPolynomial (Fin N) F))
    (hM : ∀ r t,
      esymm (Fin N) F r * B t =
        ∑ τ, aeval (fun i : Fin N ↦ expand k (esymm (Fin N) F (i + 1)))
          (M r τ t) * B τ)
    (hAF : Function.Injective (algebraMap A F))
    (MA : ℕ → Matrix ι ι (MvPolynomial (Fin N) A))
    (hMAF : ∀ r, M r = (MA r).map (MvPolynomial.map (algebraMap A F)))
    (ev : A →ₐ[ℚ] G) (M0 : ℕ → Matrix ι ι (MvPolynomial (Fin N) ℚ))
    (hMAG : ∀ r, (MA r).map (MvPolynomial.map ev.toRingHom) =
      (M0 r).map (MvPolynomial.map (algebraMap ℚ G)))
    (hM0 : ∀ r i j, (M0 r i j).HasNonnegCoeffs) :
    ∃ c : n.Partition → ℕ,
      exponentDiv k (esymmPart (Fin N) ℤ μ) =
        ∑ ν, c ν • esymmPart (Fin N) ℤ ν := by
  classical
  let l := μ.parts.toList
  have hF := trace_reverse_list_prod_eq_exponentFilter hk hζ hcard o B hBo M hM l
  have hℚ := trace_identity_over_rat_of_base_change hAF ev M MA M0 hMAF hMAG l hF
  rw [list_prod_esymm_parts_toList μ] at hℚ
  obtain ⟨hTnonneg, hTfilter⟩ :=
    trace_list_prod_hasNonnegCoeffs_and_aeval_eq M0 hM0 l hℚ
  let T : MvPolynomial (Fin N) ℚ := trace (l.map M0).reverse.prod
  have hTdiv : aeval (fun i : Fin N ↦ esymm (Fin N) ℚ (i + 1)) T =
      (k ^ N : ℚ) • exponentDiv k (esymmPart (Fin N) ℚ μ) := by
    have hTdiv' := aeval_esymm_eq_smul_exponentDiv_of_aeval_expand_eq
      (N := N) (k := k) (q := k ^ N) hk
      (by simpa only [Nat.cast_pow] using hTfilter)
    simpa only [Nat.cast_pow] using hTdiv'
  have hsymℚ : (exponentDiv k (esymmPart (Fin N) ℚ μ)).IsSymmetric :=
    (isSymmetric_esymmPart μ).exponentDiv k
  have hhomℚ : (exponentDiv k (esymmPart (Fin N) ℚ μ)).IsHomogeneous n :=
    (isHomogeneous_esymmPart μ).exponentDiv hk
  have hTnonneg' : T.HasNonnegCoeffs := hTnonneg
  have hTdiv' : aeval (fun i : Fin N ↦ esymm (Fin N) ℚ (i + 1)) T =
      ((k ^ N : ℕ) : ℚ) • exponentDiv k (esymmPart (Fin N) ℚ μ) := by
    simpa only [Nat.cast_pow] using hTdiv
  have hq := exists_nonneg_esymm_expansion_of_aeval_eq_smul
    (T := T) (f := exponentDiv k (esymmPart (Fin N) ℚ μ))
    (Nat.pow_pos hk : 0 < k ^ N) hn hTnonneg' hsymℚ hhomℚ hTdiv'
  exact exists_nat_esymm_expansion_of_map_exponentDiv_nonneg hk hn μ
    (isSymmetric_esymmPart μ) (isHomogeneous_esymmPart μ) hq

end PartitionDivision
