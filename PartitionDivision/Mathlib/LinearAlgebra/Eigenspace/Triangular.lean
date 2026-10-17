/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Eigenvectors of triangular operators

Let `b` be a basis indexed by a finite poset and let `f` be triangular with respect to `b`:
`f (b i) - d i • b i` lies in the span of the `b j` with `j < i`. If `d j ≠ d i` whenever
`j < i`, then each `i` has a unique eigenvector of the form `b i + (lower terms)`, and these
eigenvectors form a basis.

The proofs were found by Aristotle (Harmonic) and ported to this Mathlib version.

## Main declarations

* `LinearMap.exists_unique_eigenvector_of_triangular`
* `LinearMap.exists_basis_eigenvector_of_triangular`
-/

@[expose] public section

namespace LinearMap

open Submodule

/-- Coordinates of a vector in `span K (b '' S)` vanish outside `S`. -/
private lemma repr_eq_zero_of_mem_span_image
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis ι K V) {S : Set ι} {x : V} (hx : x ∈ span K (b '' S)) {j : ι}
    (hj : j ∉ S) : b.repr x j = 0 := by
  rw [b.mem_span_image] at hx
  by_contra h
  exact hj (hx (Finsupp.mem_support_iff.mpr h))

/-- The span of the strictly lower basis vectors is `f`-stable. -/
private lemma map_mem_span_lt
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [PartialOrder ι]
    (b : Module.Basis ι K V) (f : V →ₗ[K] V) (d : ι → K)
    (hf : ∀ i, f (b i) - d i • b i ∈ span K (b '' {j | j < i})) (i : ι) :
    ∀ x ∈ span K (b '' {j | j < i}), f x ∈ span K (b '' {j | j < i}) := by
  intro x hx
  have hle : span K (b '' {j | j < i}) ≤ (span K (b '' {j | j < i})).comap f := by
    rw [span_le]
    rintro _ ⟨j, hj, rfl⟩
    simp only [Set.mem_ofPred_eq] at hj
    change f (b j) ∈ span K (b '' {j | j < i})
    have h1 : f (b j) - d j • b j ∈ span K (b '' {j | j < i}) :=
      span_mono (Set.image_mono fun k (hk : k < j) => (lt_trans hk hj : k < i)) (hf j)
    have h2 : d j • b j ∈ span K (b '' {j | j < i}) :=
      smul_mem _ _ (subset_span ⟨j, hj, rfl⟩)
    simpa using add_mem h1 h2
  exact hle hx

/-- `f - d i` is injective on the span of the strictly lower basis vectors. -/
private lemma eq_zero_of_mem_span_lt
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite ι] [PartialOrder ι]
    (b : Module.Basis ι K V) (f : V →ₗ[K] V) (d : ι → K)
    (hf : ∀ i, f (b i) - d i • b i ∈ span K (b '' {j | j < i}))
    (hd : ∀ i j, j < i → d j ≠ d i) (i : ι) (w : V)
    (hw : w ∈ span K (b '' {j | j < i})) (hfw : f w - d i • w = 0) : w = 0 := by
  classical
  have := Fintype.ofFinite ι
  by_contra hne
  have hsupp : (b.repr w).support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    simpa using hne
  obtain ⟨j, hjmem, hjmax⟩ := Finset.exists_maximal hsupp
  have hjlt : j < i := (b.mem_span_image.mp hw) hjmem
  have haj : b.repr w j ≠ 0 := Finsupp.mem_support_iff.mp hjmem
  -- coordinate `j` of `f (b k)` for `k` in the support
  have hcoord : ∀ k, b.repr w k ≠ 0 →
      b.repr w k * b.repr (f (b k)) j = if k = j then b.repr w j * d j else 0 := by
    intro k hk
    have hr : b.repr (f (b k) - d k • b k) j = 0 := by
      apply repr_eq_zero_of_mem_span_image b (hf k)
      intro hjk
      simp only [Set.mem_ofPred_eq] at hjk
      exact (hjmax (Finsupp.mem_support_iff.mpr hk) hjk.le).not_gt hjk
    rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, b.repr_self,
      sub_eq_zero] at hr
    rw [hr]
    split_ifs with hkj
    · subst hkj; simp [mul_comm]
    · simp [Ne.symm hkj]
  have hfw' : b.repr (f w) j = b.repr w j * d j := by
    conv_lhs => rw [← b.sum_repr w]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [hcoord j haj, ite_eq_left rfl]
    · intro k _ hkj
      by_cases hk : b.repr w k = 0
      · simp [hk]
      · rw [hcoord k hk, ite_eq_right hkj]
    · simp
  have := congrArg (fun x => b.repr x j) hfw
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, map_zero,
    Finsupp.coe_zero, Pi.zero_apply, hfw'] at this
  have h2 : b.repr w j * (d j - d i) = 0 := by rw [mul_sub, mul_comm _ (d i)]; exact this
  rcases mul_eq_zero.mp h2 with h | h
  · exact haj h
  · exact hd i j hjlt (sub_eq_zero.mp h)

/-- A linear endomorphism that is triangular with respect to a basis indexed by a finite poset,
with diagonal entries distinct on comparable pairs, has for each index a unique eigenvector of the
form `b i + (lower terms)`. -/
theorem exists_unique_eigenvector_of_triangular
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite ι] [PartialOrder ι]
    (b : Module.Basis ι K V) (f : V →ₗ[K] V) (d : ι → K)
    (hf : ∀ i, f (b i) - d i • b i ∈ span K (b '' {j | j < i}))
    (hd : ∀ i j, j < i → d j ≠ d i) (i : ι) :
    ∃! v : V, v - b i ∈ span K (b '' {j | j < i}) ∧ f v = d i • v := by
  have := Fintype.ofFinite ι
  have : FiniteDimensional K V := Module.Finite.of_basis b
  set W := span K (b '' {j | j < i}) with hW
  set g : V →ₗ[K] V := f - d i • LinearMap.id with hg
  have hgW : ∀ x ∈ W, g x ∈ W := by
    intro x hx
    simp only [hg, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact sub_mem (map_mem_span_lt b f d hf i x hx) (smul_mem _ _ hx)
  let gW : W →ₗ[K] W := g.restrict hgW
  have hinj : Function.Injective gW := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h := congrArg Subtype.val hw
    simp only [gW, LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero, hg,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
    exact Subtype.ext (eq_zero_of_mem_span_lt b f d hf hd i w w.2 h)
  have hsurj : Function.Surjective gW := LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨w, hw⟩ := hsurj ⟨-(f (b i) - d i • b i), neg_mem (hf i)⟩
  have hw' : f (w : V) - d i • (w : V) = -(f (b i) - d i • b i) := by
    have h := congrArg Subtype.val hw
    simpa only [gW, LinearMap.coe_restrict_apply, hg, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply] using h
  refine ⟨b i + w, ⟨by simp, ?_⟩, ?_⟩
  · rw [map_add, smul_add]
    have : f (b i) + f (w : V) - (d i • b i + d i • (w : V)) = 0 := by
      rw [show f (b i) + f (w : V) - (d i • b i + d i • (w : V))
        = (f (b i) - d i • b i) + (f (w : V) - d i • (w : V)) by abel, hw']
      abel
    exact sub_eq_zero.mp this
  · rintro v ⟨hv1, hv2⟩
    have hmem : v - (b i + w) ∈ W := by
      rw [show v - (b i + w) = (v - b i) - w by abel]
      exact sub_mem hv1 w.2
    have hker : f (v - (b i + w)) - d i • (v - (b i + w)) = 0 := by
      rw [map_sub, map_add, hv2, smul_sub, smul_add]
      rw [show d i • v - (f (b i) + f (w : V)) - (d i • v - (d i • b i + d i • (w : V)))
        = -((f (b i) - d i • b i) + (f (w : V) - d i • (w : V))) by abel, hw']
      abel
    exact sub_eq_zero.mp (eq_zero_of_mem_span_lt b f d hf hd i _ hmem hker)

/-- The unitriangular eigenvectors form a basis. -/
theorem exists_basis_eigenvector_of_triangular
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite ι] [PartialOrder ι]
    (b : Module.Basis ι K V) (f : V →ₗ[K] V) (d : ι → K)
    (hf : ∀ i, f (b i) - d i • b i ∈ span K (b '' {j | j < i}))
    (hd : ∀ i j, j < i → d j ≠ d i) :
    ∃ c : Module.Basis ι K V, ∀ i, c i - b i ∈ span K (b '' {j | j < i}) ∧
      f (c i) = d i • c i := by
  classical
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨b, fun i => isEmptyElim i⟩
  choose c hc using fun i => (exists_unique_eigenvector_of_triangular b f d hf hd i).exists
  have hli : LinearIndependent K c := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    have hsupp : (Finset.univ.filter fun k => g k ≠ 0).Nonempty := by
      obtain ⟨k, hk⟩ := hne
      exact ⟨k, by simpa using hk⟩
    obtain ⟨j, hjmem, hjmax⟩ := Finset.exists_maximal hsupp
    have hgj : g j ≠ 0 := by simpa using hjmem
    have hcoord : ∀ k, g k * b.repr (c k) j = if k = j then g j else 0 := by
      intro k
      by_cases hk : g k = 0
      · split_ifs with hkj
        · subst hkj; simp [hk]
        · simp [hk]
      have hr : b.repr (c k - b k) j = 0 := by
        apply repr_eq_zero_of_mem_span_image b (hc k).1
        intro hjk
        simp only [Set.mem_ofPred_eq] at hjk
        exact (hjmax (by simpa using hk) hjk.le).not_gt hjk
      rw [map_sub, Finsupp.sub_apply, b.repr_self, sub_eq_zero] at hr
      rw [hr]
      split_ifs with hkj
      · subst hkj; simp
      · simp [Ne.symm hkj]
    have := congrArg (fun x => b.repr x j) hg
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply,
      hcoord, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
    exact hgj this
  have hcard : Fintype.card ι = Module.finrank K V := (Module.finrank_eq_card_basis b).symm
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, fun i => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact hc i

end LinearMap
