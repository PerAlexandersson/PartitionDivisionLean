/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import PartitionDivision.Macdonald.Basic
public import PartitionDivision.Macdonald.EvaluationSymmetry
public import PartitionDivision.Macdonald.GridDeterminant
public import PartitionDivision.Macdonald.GridEvaluation
public import PartitionDivision.Macdonald.PieriCoefficient

/-!
# The evaluation-symmetry induction for the Macdonald polynomials

This file instantiates the abstract simultaneous induction
`Macdonald.EvaluationPieriData.normalized_symmetry_and_pieri` (Pieri ledger Lemma 12) for the
Macdonald polynomials `MvPolynomial.macdonaldP` over `ℚ(q, t)`, ordered by size and then
lexicographically.

* Indices are partition vectors, the base index is `0`, and steps are natural numbers `s`
  (multiplication by `esymm s`).
* The successors of `μ` for the step `s` are the partition vectors `μ + 1_I` for the legal row
  subsets `I` with `#I = s`; the coefficient of `μ + 1_I` is the grid coefficient `B μ I`.
* The chosen decomposition of `μ ≠ 0` removes its first column: `parent μ = μ - 1`
  (coordinatewise, truncated) and `step μ` is the number of positive parts of `μ`.

The structural hypotheses are proved here: well-foundedness, the first-column decomposition,
the lower expansions (from lexicographic unitriangularity of `macdonaldP`), and separation by
evaluation on lower grids (from the nonsingular orbit-sum grid matrix).  The grid recurrence
(ledger Lemma 10 for `macdonaldP`, which depends on the joint spectral action of Lemma 7) and the
nonvanishing of the base evaluation (ledger Lemma 8) remain hypotheses of the final theorem
`macdonaldP_normalized_symmetry_and_pieri`.
-/

@[expose] public section

noncomputable section

open Finset

/-- The field `ℚ(q, t)` of rational functions in the Macdonald parameters. -/
local notation "𝕂" => FractionRing (MvPolynomial (Fin 2) ℚ)

namespace MvPolynomial

variable {N : ℕ}

/-- The finitely supported exponent vector of a partition vector determines it. -/
theorem partitionVectorFinsupp_injective :
    Function.Injective (partitionVectorFinsupp : Nat.PartitionVector N → Fin N →₀ ℕ) := by
  intro a b h
  apply Nat.PartitionVector.ext
  intro i
  simpa using congrArg (fun d : Fin N →₀ ℕ ↦ d i) h

/-- Every exponent of an element of the span of some `msymmVec κ` is a rearrangement of one of
the indices `κ`. -/
theorem exists_mem_rearrangements_of_mem_span_msymmVec {K : Type*} [CommSemiring K]
    {S : Set (Nat.PartitionVector N)} {x : MvPolynomial (Fin N) K}
    (hx : x ∈ Submodule.span K (msymmVec K '' S)) :
    ∀ b ∈ x.support, ∃ kappa ∈ S, b ∈ partitionVectorRearrangements kappa := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨kappa, hkappa, rfl⟩ := hy
      intro b hb
      refine ⟨kappa, hkappa, ?_⟩
      rw [mem_support_iff, coeff_msymmVec] at hb
      by_contra h
      simp [h] at hb
  | zero => simp
  | add y z _ _ hy hz =>
      intro b hb
      rcases Finset.mem_union.mp (support_add hb) with h | h
      exacts [hy b h, hz b h]
  | smul c y _ hy =>
      intro b hb
      exact hy b (support_smul hb)

/-- The lower part of `macdonaldP λ` only has exponents lexicographically below `λ`. -/
theorem toLex_lt_of_mem_support_macdonaldP_sub_msymmVec (lambda : Nat.PartitionVector N)
    {b : Fin N →₀ ℕ} (hb : b ∈ (macdonaldP lambda - msymmVec 𝕂 lambda).support) :
    toLex b < toLex (partitionVectorFinsupp lambda) := by
  obtain ⟨kappa, hkappa, hb'⟩ := exists_mem_rearrangements_of_mem_span_msymmVec
    (macdonaldP_sub_msymmVec_mem_span lambda) b hb
  exact (toLex_le_partitionVectorFinsupp_of_mem hb').trans_lt hkappa.2

/-- Every exponent of `macdonaldP λ` is lexicographically at most `λ`. -/
theorem toLex_le_of_mem_support_macdonaldP {lambda : Nat.PartitionVector N}
    {b : Fin N →₀ ℕ} (hb : b ∈ (macdonaldP lambda).support) :
    toLex b ≤ toLex (partitionVectorFinsupp lambda) := by
  classical
  have hsplit : macdonaldP lambda =
      msymmVec 𝕂 lambda + (macdonaldP lambda - msymmVec 𝕂 lambda) := by
    rw [add_sub_cancel]
  rw [hsplit] at hb
  rcases Finset.mem_union.mp (support_add hb) with h | h
  · rw [mem_support_iff, coeff_msymmVec] at h
    split_ifs at h with hm
    · exact toLex_le_partitionVectorFinsupp_of_mem hm
    · exact absurd rfl h
  · exact (toLex_lt_of_mem_support_macdonaldP_sub_msymmVec lambda h).le

/-- The coefficient of `macdonaldP λ` at `λ` is one. -/
theorem coeff_macdonaldP_self (lambda : Nat.PartitionVector N) :
    (macdonaldP lambda).coeff (partitionVectorFinsupp lambda) = 1 := by
  have h : (macdonaldP lambda - msymmVec 𝕂 lambda).coeff (partitionVectorFinsupp lambda) = 0 := by
    by_contra hne
    exact lt_irrefl _
      (toLex_lt_of_mem_support_macdonaldP_sub_msymmVec lambda (mem_support_iff.mpr hne))
  rw [coeff_sub, coeff_msymmVec_partitionVectorFinsupp, sub_eq_zero] at h
  simpa using h

/-- The Macdonald polynomials are linearly independent. -/
theorem linearIndependent_macdonaldP :
    LinearIndependent 𝕂 (macdonaldP : Nat.PartitionVector N → MvPolynomial (Fin N) 𝕂) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hne
  have hs : (s.filter fun j ↦ g j ≠ 0).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hne⟩⟩
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image (s.filter fun j ↦ g j ≠ 0)
    (fun j ↦ toLex (partitionVectorFinsupp j)) hs
  have hc : ∑ j ∈ s, g j * (macdonaldP j).coeff (partitionVectorFinsupp k) = 0 := by
    have h := congrArg (fun p : MvPolynomial (Fin N) 𝕂 ↦ p.coeff (partitionVectorFinsupp k)) hg
    simpa [coeff_sum] using h
  rw [Finset.sum_eq_single k] at hc
  · rw [coeff_macdonaldP_self, mul_one] at hc
    exact (Finset.mem_filter.mp hk).2 hc
  · intro j hj hjk
    by_cases hgj : g j = 0
    · simp [hgj]
    · have hjle := hkmax j (Finset.mem_filter.mpr ⟨hj, hgj⟩)
      have hcoeff : (macdonaldP j).coeff (partitionVectorFinsupp k) = 0 := by
        by_contra hc0
        have hle := toLex_le_of_mem_support_macdonaldP (mem_support_iff.mpr hc0)
        apply hjk
        exact partitionVectorFinsupp_injective (toLex.injective (le_antisymm hle hjle)).symm
      rw [hcoeff, mul_zero]
  · intro hk'
    exact absurd (Finset.mem_filter.mp hk).1 hk'

/-- A set of partition vectors is closed under lexicographically smaller vectors of the same
size. -/
def IsLexLowerClosed (L : Set (Nat.PartitionVector N)) : Prop :=
  ∀ nu ∈ L, ∀ kappa, partitionVectorDegree kappa = partitionVectorDegree nu →
    toLex (partitionVectorFinsupp kappa) < toLex (partitionVectorFinsupp nu) → kappa ∈ L

/-- On a lexicographically lower-closed set, every `macdonaldP` lies in the monomial span. -/
theorem span_macdonaldP_image_le {L : Set (Nat.PartitionVector N)} (hL : IsLexLowerClosed L) :
    Submodule.span 𝕂 (macdonaldP '' L) ≤ Submodule.span 𝕂 (msymmVec 𝕂 '' L) := by
  rw [Submodule.span_le]
  rintro _ ⟨nu, hnu, rfl⟩
  have hsplit : macdonaldP nu = msymmVec 𝕂 nu + (macdonaldP nu - msymmVec 𝕂 nu) := by
    rw [add_sub_cancel]
  rw [SetLike.mem_coe, hsplit]
  refine Submodule.add_mem _ (Submodule.subset_span ⟨nu, hnu, rfl⟩) ?_
  refine Submodule.span_mono ?_ (macdonaldP_sub_msymmVec_mem_span nu)
  rintro _ ⟨kappa, hkappa, rfl⟩
  exact ⟨kappa, hL nu hnu kappa hkappa.1 hkappa.2, rfl⟩

/-- On a lexicographically lower-closed set, every `msymmVec` lies in the span of the Macdonald
polynomials. -/
theorem msymmVec_mem_span_macdonaldP {L : Set (Nat.PartitionVector N)}
    (hL : IsLexLowerClosed L) {kappa : Nat.PartitionVector N} (hkappa : kappa ∈ L) :
    msymmVec 𝕂 kappa ∈ Submodule.span 𝕂 (macdonaldP '' L) := by
  suffices h : ∀ x : Lex (Fin N →₀ ℕ), ∀ kappa ∈ L,
      toLex (partitionVectorFinsupp kappa) = x →
        msymmVec 𝕂 kappa ∈ Submodule.span 𝕂 (macdonaldP '' L) from
    h _ kappa hkappa rfl
  intro x
  induction x using WellFoundedLT.induction with
  | _ x ih =>
      intro kappa hkappa hx
      have hsplit : msymmVec 𝕂 kappa =
          macdonaldP kappa - (macdonaldP kappa - msymmVec 𝕂 kappa) := by
        rw [sub_sub_cancel]
      rw [hsplit]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨kappa, hkappa, rfl⟩) ?_
      refine (Submodule.span_le.mpr ?_) (macdonaldP_sub_msymmVec_mem_span kappa)
      rintro _ ⟨nu, hnu, rfl⟩
      exact ih _ (hx ▸ hnu.2) nu (hL kappa hkappa nu hnu.1 hnu.2) rfl

/-- On a lexicographically lower-closed set, the Macdonald polynomials and the monomial
symmetric polynomials span the same space. -/
theorem span_macdonaldP_image_eq {L : Set (Nat.PartitionVector N)} (hL : IsLexLowerClosed L) :
    Submodule.span 𝕂 (macdonaldP '' L) = Submodule.span 𝕂 (msymmVec 𝕂 '' L) := by
  refine le_antisymm (span_macdonaldP_image_le hL) ?_
  rw [Submodule.span_le]
  rintro _ ⟨kappa, hkappa, rfl⟩
  exact msymmVec_mem_span_macdonaldP hL hkappa

/-- The partition vector `0` has `msymmVec` equal to one. -/
theorem msymmVec_zero (K : Type*) [CommSemiring K] :
    msymmVec K (0 : Nat.PartitionVector N) = 1 := by
  classical
  have h : partitionVectorRearrangements (0 : Nat.PartitionVector N) = {0} := by
    ext d
    rw [mem_partitionVectorRearrangements_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨e, rfl⟩
      ext i
      simp
    · rintro rfl
      refine ⟨1, ?_⟩
      ext i
      simp
  rw [msymmVec, h, Finset.sum_singleton, ← C_1, C_apply]

/-- The Macdonald polynomial of the empty partition is one. -/
theorem macdonaldP_zero : macdonaldP (0 : Nat.PartitionVector N) = 1 := by
  have hempty : lexLowerPartitionVectors (partitionVectorDegree (0 : Nat.PartitionVector N))
      (0 : Nat.PartitionVector N) = ∅ := by
    ext kappa
    simp only [lexLowerPartitionVectors, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_and]
    intro hdeg hlt
    have hk : kappa = 0 := by
      apply Nat.PartitionVector.ext
      intro i
      have hle : kappa i ≤ ∑ j, kappa j :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      have hsum : ∑ j, kappa j = 0 := by
        simpa [partitionVectorDegree] using hdeg
      simp only [Nat.PartitionVector.zero_apply]
      lia
    subst hk
    exact lt_irrefl _ hlt
  have h := macdonaldP_sub_msymmVec_mem_span (0 : Nat.PartitionVector N)
  rw [hempty, Set.image_empty, Submodule.span_empty, Submodule.mem_bot, sub_eq_zero] at h
  rw [h, msymmVec_zero]

/-- The elementary symmetric polynomial `esymm s` is homogeneous of degree `s`. -/
theorem isHomogeneous_esymm (K : Type*) [CommSemiring K] (s : ℕ) :
    (esymm (Fin N) K s).IsHomogeneous s := by
  rw [esymm]
  apply IsHomogeneous.sum
  intro t ht
  have h := IsHomogeneous.prod t (fun i ↦ (X i : MvPolynomial (Fin N) K)) (fun _ ↦ 1)
    (fun i _ ↦ isHomogeneous_X K i)
  simpa [(Finset.mem_powersetCard.mp ht).2] using h

/-- Evaluating a monomial symmetric polynomial is the orbit sum used by the grid determinant. -/
theorem eval_msymmVec_eq_orbitSum {R : Type*} [CommSemiring R]
    (kappa : Nat.PartitionVector N) (x : Fin N → R) :
    eval x (msymmVec R kappa) = PartitionDivision.Macdonald.orbitSum kappa x := by
  classical
  rw [msymmVec, map_sum, PartitionDivision.Macdonald.orbitSum]
  refine Finset.sum_nbij' (fun d ↦ ⇑d) (fun β ↦ Finsupp.equivFunOnFinite.symm β)
    ?_ ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨e, rfl⟩ := (mem_partitionVectorRearrangements_iff _ _).mp hd
    simp only [Nat.PartitionVector.rearrangements, Finset.mem_image,
      Finset.mem_univ, true_and]
    refine ⟨e.symm, ?_⟩
    funext i
    simp [Finsupp.mapDomain_equiv_apply]
  · intro β hβ
    simp only [Nat.PartitionVector.rearrangements, Finset.mem_image,
      Finset.mem_univ, true_and] at hβ
    obtain ⟨σ, rfl⟩ := hβ
    rw [mem_partitionVectorRearrangements_iff]
    refine ⟨σ.symm, ?_⟩
    ext i
    simp [Finsupp.mapDomain_equiv_apply]
  · intro d _
    simp
  · intro β _
    simp
  · intro d _
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), one_mul]

end MvPolynomial

namespace Macdonald

open MvPolynomial

variable {N : ℕ}

/-! ### Combinatorics of the instance -/

/-- Size first, then lexicographic order. -/
def SizeLexLT (nu mu : Nat.PartitionVector N) : Prop :=
  partitionVectorDegree nu < partitionVectorDegree mu ∨
    (partitionVectorDegree nu = partitionVectorDegree mu ∧
      toLex (partitionVectorFinsupp nu) < toLex (partitionVectorFinsupp mu))

/-- The size-then-lexicographic relation is well-founded. -/
theorem wellFounded_sizeLexLT : WellFounded (SizeLexLT (N := N)) := by
  have h := InvImage.wf
    (fun nu : Nat.PartitionVector N ↦
      (partitionVectorDegree nu, toLex (partitionVectorFinsupp nu)))
    (WellFounded.prod_lex (wellFounded_lt (α := ℕ))
      (wellFounded_lt (α := Lex (Fin N →₀ ℕ))))
  refine Subrelation.wf (fun {a b} hab ↦ ?_) h
  rcases hab with hlt | ⟨heq, hlt⟩
  · exact Prod.Lex.left _ _ hlt
  · change Prod.Lex _ _ (partitionVectorDegree a, _) (partitionVectorDegree b, _)
    rw [heq]
    exact Prod.Lex.right _ hlt

/-- The number of positive parts of a partition vector. -/
def numParts (mu : Nat.PartitionVector N) : ℕ :=
  #(Finset.univ.filter fun i ↦ 0 < mu i)

/-- The rows in which a partition vector is positive. -/
def posParts (mu : Nat.PartitionVector N) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ 0 < mu i

/-- The positive parts of a partition vector are its first `numParts` rows. -/
theorem lt_numParts_iff (mu : Nat.PartitionVector N) (i : Fin N) :
    i.val < numParts mu ↔ 0 < mu i :=
  Tuple.lt_card_gt_iff_apply_gt_of_antitone mu.antitone

/-- Remove the first column: subtract one from every positive part. -/
def removeColumn (mu : Nat.PartitionVector N) : Nat.PartitionVector N :=
  ⟨fun i ↦ mu i - 1, fun _ _ hij ↦ Nat.sub_le_sub_right (mu.antitone hij) 1⟩

@[simp]
theorem removeColumn_apply (mu : Nat.PartitionVector N) (i : Fin N) :
    removeColumn mu i = mu i - 1 :=
  rfl

/-- Adding back the positive rows to the column-removed vector recovers the vector. -/
theorem increment_removeColumn (mu : Nat.PartitionVector N) :
    Nat.PartitionVector.Macdonald.increment (removeColumn mu) (posParts mu) = mu := by
  funext i
  simp only [Nat.PartitionVector.Macdonald.increment, removeColumn_apply, posParts,
    Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h <;> lia

/-- The positive rows form a legal strip on the column-removed vector. -/
theorem isLegal_removeColumn (mu : Nat.PartitionVector N) :
    Nat.PartitionVector.Macdonald.IsLegal (removeColumn mu) (posParts mu) := by
  rw [Nat.PartitionVector.Macdonald.IsLegal, increment_removeColumn]
  exact mu.antitone

/-- The sum of a partition vector is the sum of its column-removed vector and its number of
positive parts. -/
theorem partitionVectorDegree_removeColumn (mu : Nat.PartitionVector N) :
    partitionVectorDegree (removeColumn mu) + numParts mu = partitionVectorDegree mu := by
  rw [partitionVectorDegree, partitionVectorDegree, numParts, Finset.card_filter,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [removeColumn_apply]
  split_ifs with h <;> lia

/-- A nonzero partition vector has a positive part. -/
theorem numParts_pos {mu : Nat.PartitionVector N} (hmu : mu ≠ 0) : 0 < numParts mu := by
  by_contra h
  apply hmu
  apply Nat.PartitionVector.ext
  intro i
  have h' : ¬ i.val < numParts mu := by lia
  rw [lt_numParts_iff] at h'
  simp only [Nat.PartitionVector.zero_apply]
  lia

/-- Adding the first column `1 ^ numParts` back to the column-removed vector recovers it. -/
theorem removeColumn_add_prefixOnes (mu : Nat.PartitionVector N) :
    removeColumn mu + Nat.PartitionVector.Pieri.prefixOnes (numParts mu) = mu := by
  apply Nat.PartitionVector.ext
  intro i
  simp only [Nat.PartitionVector.add_apply, removeColumn_apply,
    Nat.PartitionVector.Pieri.prefixOnes_apply]
  have h := lt_numParts_iff mu i
  split_ifs with hi <;> grind

/-- Removing the first column of a nonzero vector decreases the size. -/
theorem sizeLexLT_removeColumn {mu : Nat.PartitionVector N} (hmu : mu ≠ 0) :
    SizeLexLT (removeColumn mu) mu := by
  left
  have h := partitionVectorDegree_removeColumn mu
  have hpos := numParts_pos hmu
  lia

/-- Add the rows in `I` if this gives a partition vector; otherwise return `μ` (a junk value
which never occurs below). -/
def addStrip (mu : Nat.PartitionVector N) (I : Finset (Fin N)) : Nat.PartitionVector N := by
  classical
  exact if h : Nat.PartitionVector.Macdonald.IsLegal mu I then
      Nat.PartitionVector.Macdonald.incrementPartition mu I h
    else mu

theorem addStrip_of_isLegal {mu : Nat.PartitionVector N} {I : Finset (Fin N)}
    (h : Nat.PartitionVector.Macdonald.IsLegal mu I) :
    addStrip mu I = Nat.PartitionVector.Macdonald.incrementPartition mu I h := by
  simp [addStrip, h]

/-- The legal vertical strips of size `s` on `μ`, as partition vectors. -/
def stripSuccessors (mu : Nat.PartitionVector N) (s : ℕ) : Finset (Nat.PartitionVector N) := by
  classical
  exact ((Finset.univ.powersetCard s).filter
    fun I ↦ Nat.PartitionVector.Macdonald.IsLegal mu I).image (addStrip mu)

theorem mem_stripSuccessors {mu nu : Nat.PartitionVector N} {s : ℕ} :
    nu ∈ stripSuccessors mu s ↔ ∃ I : Finset (Fin N), I.card = s ∧
      ∃ h : Nat.PartitionVector.Macdonald.IsLegal mu I,
        Nat.PartitionVector.Macdonald.incrementPartition mu I h = nu := by
  classical
  simp only [stripSuccessors, Finset.mem_image, Finset.mem_filter, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]
  constructor
  · rintro ⟨I, ⟨hcard, hI⟩, rfl⟩
    exact ⟨I, hcard, hI, (addStrip_of_isLegal hI).symm⟩
  · rintro ⟨I, hcard, hI, rfl⟩
    exact ⟨I, ⟨hcard, hI⟩, addStrip_of_isLegal hI⟩

/-- The exponent vector of an incremented partition vector. -/
theorem partitionVectorFinsupp_incrementPartition (mu : Nat.PartitionVector N)
    (I : Finset (Fin N)) (h : Nat.PartitionVector.Macdonald.IsLegal mu I) :
    partitionVectorFinsupp (Nat.PartitionVector.Macdonald.incrementPartition mu I h) =
      partitionVectorFinsupp mu + ∑ i ∈ I, Finsupp.single i 1 := by
  classical
  ext j
  simp [Finsupp.single_apply]

/-- The size of an incremented partition vector. -/
theorem partitionVectorDegree_incrementPartition (mu : Nat.PartitionVector N)
    (I : Finset (Fin N)) (h : Nat.PartitionVector.Macdonald.IsLegal mu I) :
    partitionVectorDegree (Nat.PartitionVector.Macdonald.incrementPartition mu I h) =
      partitionVectorDegree mu + I.card := by
  classical
  simp only [partitionVectorDegree, Nat.PartitionVector.Macdonald.incrementPartition_apply,
    Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
  congr 2
  ext i
  simp

/-- **The initial column is the lexicographically greatest strip.**  The indicator of any `s`
rows is lexicographically at most the indicator `1 ^ s` of the first `s` rows. -/
theorem toLex_sum_single_le_prefixOnes (I : Finset (Fin N)) :
    toLex (∑ i ∈ I, Finsupp.single i 1) ≤
      toLex (partitionVectorFinsupp (Nat.PartitionVector.Pieri.prefixOnes (N := N) I.card)) := by
  classical
  rw [← not_lt, Finsupp.Lex.lt_iff]
  rintro ⟨i, hlow, hi⟩
  simp only [ofLex_toLex, partitionVectorFinsupp_apply,
    Nat.PartitionVector.Pieri.prefixOnes_apply, Finsupp.finsetSum_apply,
    Finsupp.single_apply, Finset.sum_ite_eq'] at hlow hi
  have hiI : i ∈ I := by
    by_contra h
    simp [h] at hi
  have hic : ¬ i.val < I.card := by
    intro h
    simp [h, hiI] at hi
  have hsub : (Finset.univ.filter fun j : Fin N ↦ (j : ℕ) < I.card) ∪ {i} ⊆ I := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · have hjc : (j : ℕ) < I.card := (Finset.mem_filter.mp hj).2
      have hji : j < i := by
        rw [Fin.lt_def]
        lia
      have := hlow j hji
      by_contra hjI
      simp [hjc, hjI] at this
    · rw [Finset.mem_singleton.mp hj]
      exact hiI
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint, Fin.card_filter_val_lt, Finset.card_singleton] at hcard
  · have hN : I.card ≤ N := by
      have := Finset.card_le_univ I
      simpa using this
    lia
  · rw [Finset.disjoint_singleton_right]
    simp [hic]

/-- Every legal strip of size `s` on `μ` is lexicographically at most `μ + 1 ^ s`. -/
theorem toLex_incrementPartition_le (mu : Nat.PartitionVector N) (I : Finset (Fin N))
    (h : Nat.PartitionVector.Macdonald.IsLegal mu I) :
    toLex (partitionVectorFinsupp (Nat.PartitionVector.Macdonald.incrementPartition mu I h)) ≤
      toLex (partitionVectorFinsupp (mu + Nat.PartitionVector.Pieri.prefixOnes I.card)) := by
  have hadd : partitionVectorFinsupp (mu + Nat.PartitionVector.Pieri.prefixOnes I.card) =
      partitionVectorFinsupp mu +
        partitionVectorFinsupp (Nat.PartitionVector.Pieri.prefixOnes (N := N) I.card) := by
    ext j
    simp
  rw [partitionVectorFinsupp_incrementPartition, hadd, toLex_add, toLex_add]
  exact add_le_add le_rfl (toLex_sum_single_le_prefixOnes I)

/-- The finite set of partition vectors of size `n` lexicographically at most `λ`. -/
def lexLowerFinset (n : ℕ) (lambda : Nat.PartitionVector N) : Finset (Nat.PartitionVector N) :=
  (Set.Finite.subset (s := {mu : Nat.PartitionVector N | partitionVectorDegree mu = n})
    (Set.finite_coe_iff.mp
      (show Finite {mu : Nat.PartitionVector N | partitionVectorDegree mu = n} from
        finite_partitionVectorDegree n))
    (t := {mu | partitionVectorDegree mu = n ∧
      toLex (partitionVectorFinsupp mu) ≤ toLex (partitionVectorFinsupp lambda)})
    (fun _ hmu ↦ hmu.1)).toFinset

@[simp]
theorem mem_lexLowerFinset {n : ℕ} {lambda mu : Nat.PartitionVector N} :
    mu ∈ lexLowerFinset n lambda ↔ partitionVectorDegree mu = n ∧
      toLex (partitionVectorFinsupp mu) ≤ toLex (partitionVectorFinsupp lambda) := by
  rw [lexLowerFinset, Set.Finite.mem_toFinset]
  rfl

/-- The sets `lexLowerFinset n λ` are lexicographically lower-closed. -/
theorem isLexLowerClosed_lexLowerFinset (n : ℕ) (lambda : Nat.PartitionVector N) :
    IsLexLowerClosed (lexLowerFinset n lambda : Set (Nat.PartitionVector N)) := by
  intro nu hnu kappa hdeg hlt
  rw [Finset.mem_coe, mem_lexLowerFinset] at hnu ⊢
  exact ⟨hdeg.trans hnu.1, hlt.le.trans hnu.2⟩

/-- The lower set used for the Pieri pair `(μ, s)`. -/
def lowerPS (mu : Nat.PartitionVector N) (s : ℕ) : Finset (Nat.PartitionVector N) :=
  lexLowerFinset (partitionVectorDegree mu + s) (mu + Nat.PartitionVector.Pieri.prefixOnes s)

/-- The lower set used for the symmetry step at `top`. -/
def lowerTop (top : Nat.PartitionVector N) : Finset (Nat.PartitionVector N) :=
  lexLowerFinset (partitionVectorDegree top) top

/-- For the first-column decomposition, the Pieri lower set is the symmetry lower set. -/
theorem lowerPS_removeColumn (mu : Nat.PartitionVector N) :
    lowerPS (removeColumn mu) (numParts mu) = lowerTop mu := by
  rw [lowerPS, lowerTop, partitionVectorDegree_removeColumn, removeColumn_add_prefixOnes]

/-- Every legal strip successor lies in the Pieri lower set. -/
theorem stripSuccessors_subset_lowerPS (mu : Nat.PartitionVector N) (s : ℕ) :
    stripSuccessors mu s ⊆ lowerPS mu s := by
  intro nu hnu
  obtain ⟨I, hcard, hI, rfl⟩ := mem_stripSuccessors.mp hnu
  rw [lowerPS, mem_lexLowerFinset, partitionVectorDegree_incrementPartition, hcard]
  refine ⟨rfl, ?_⟩
  have h := toLex_incrementPartition_le mu I hI
  rwa [hcard] at h

/-- Membership in a symmetry lower set is either equality or a strict decrease. -/
theorem eq_or_sizeLexLT_of_mem_lowerTop {nu mu : Nat.PartitionVector N}
    (h : nu ∈ lowerTop mu) : nu = mu ∨ SizeLexLT nu mu := by
  rw [lowerTop, mem_lexLowerFinset] at h
  rcases h.2.lt_or_eq with hlt | heq
  · exact Or.inr (Or.inr ⟨h.1, hlt⟩)
  · exact Or.inl (partitionVectorFinsupp_injective (toLex.injective heq))

/-- A partition vector is a strip successor of its column-removed vector. -/
theorem mem_stripSuccessors_removeColumn (mu : Nat.PartitionVector N) :
    mu ∈ stripSuccessors (removeColumn mu) (numParts mu) := by
  rw [mem_stripSuccessors]
  refine ⟨posParts mu, rfl, isLegal_removeColumn mu, ?_⟩
  apply Nat.PartitionVector.ext
  intro i
  exact congrFun (increment_removeColumn mu) i

/-! ### The data of the instance -/

/-- The parameter pair `(q, t)` is power-pair injective. -/
theorem powerPairInjective_macdonaldParam :
    Nat.PartitionVector.Macdonald.PowerPairInjective (macdonaldParamQ : 𝕂) macdonaldParamT :=
  Nat.PartitionVector.Macdonald.powerPairInjective_fractionRing

/-- The evaluation grid `x_i = q ^ μ i t ^ (N - 1 - i)` at the Macdonald parameters. -/
abbrev pieriGrid (mu : Nat.PartitionVector N) : Fin N → 𝕂 :=
  Nat.PartitionVector.Macdonald.grid macdonaldParamQ macdonaldParamT mu

/-- The coefficient attached to a strip successor: the grid coefficient `B` of its rows. -/
def stripCoeff (mu : Nat.PartitionVector N) (_s : ℕ) (nu : Nat.PartitionVector N) : 𝕂 :=
  Nat.PartitionVector.Macdonald.B macdonaldParamQ macdonaldParamT mu
    (Finset.univ.filter fun i ↦ mu i < nu i)

/-- The rows in which an incremented vector exceeds the original are the incremented rows. -/
theorem filter_lt_incrementPartition (mu : Nat.PartitionVector N) (I : Finset (Fin N))
    (h : Nat.PartitionVector.Macdonald.IsLegal mu I) :
    (Finset.univ.filter fun i ↦
      mu i < Nat.PartitionVector.Macdonald.incrementPartition mu I h i) = I := by
  ext i
  by_cases hi : i ∈ I <;> simp [hi]

/-- The evaluation--Pieri data of the Macdonald polynomials. -/
def pieriData : EvaluationPieriData (K := 𝕂) (A := MvPolynomial (Fin N) 𝕂)
    (I := Nat.PartitionVector N) (S := ℕ) where
  eval mu := aeval (pieriGrid mu)
  p := macdonaldP
  elem s := esymm (Fin N) 𝕂 s
  next := stripSuccessors
  coeff := stripCoeff

@[simp]
theorem pieriData_eval (mu : Nat.PartitionVector N) (f : MvPolynomial (Fin N) 𝕂) :
    (pieriData.eval mu) f = eval (pieriGrid mu) f := by
  simp [pieriData]

/-- The coefficient of the first-column successor is nonzero. -/
theorem stripCoeff_removeColumn_ne_zero (mu : Nat.PartitionVector N) :
    stripCoeff (removeColumn mu) (numParts mu) mu ≠ 0 := by
  have hfilter : (Finset.univ.filter fun i ↦ removeColumn mu i < mu i) = posParts mu := by
    ext i
    rw [posParts, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, removeColumn_apply]
    lia
  rw [stripCoeff, hfilter]
  exact (Nat.PartitionVector.Macdonald.gridCoefficient_ne_zero_iff
    powerPairInjective_macdonaldParam _ _).mpr (isLegal_removeColumn mu)

/-! ### Lower expansions -/

/-- `esymm s` evaluated on a partition grid is the `s`-th Macdonald eigenvalue there. -/
theorem eval_esymm_pieriGrid (lambda : Nat.PartitionVector N) (s : ℕ) :
    eval (pieriGrid lambda) (esymm (Fin N) 𝕂 s) =
      macdonaldEigenvalueR macdonaldParamQ macdonaldParamT s lambda := by
  simp [esymm, macdonaldEigenvalueR, Nat.PartitionVector.Macdonald.grid]

/-- **Span hypothesis.**  `P_μ e_s` is a combination of the `P_ν` with `ν` of size `|μ| + s`
lexicographically at most `μ + 1 ^ s`. -/
theorem macdonaldP_mul_esymm_mem_span (mu : Nat.PartitionVector N) (s : ℕ) :
    macdonaldP mu * esymm (Fin N) 𝕂 s ∈
      Submodule.span 𝕂 (macdonaldP '' (lowerPS mu s : Set (Nat.PartitionVector N))) := by
  classical
  rw [lowerPS, span_macdonaldP_image_eq (isLexLowerClosed_lexLowerFinset _ _)]
  have hsym : (macdonaldP mu * esymm (Fin N) 𝕂 s).IsSymmetric :=
    (macdonaldP_isSymmetric mu).mul (esymm_isSymmetric (Fin N) 𝕂 s)
  have hhom : (macdonaldP mu * esymm (Fin N) 𝕂 s).IsHomogeneous
      (partitionVectorDegree mu + s) :=
    (isHomogeneous_macdonaldP mu).mul (isHomogeneous_esymm 𝕂 s)
  refine hsym.mem_span_msymmVec fun kappa hkappa ↦ ?_
  rw [Finset.mem_coe, mem_lexLowerFinset]
  refine ⟨hhom.partitionVectorDegree_eq hkappa, ?_⟩
  obtain ⟨b1, hb1, b2, hb2, hsum⟩ := Finset.mem_add.mp (support_mul _ _ hkappa)
  rw [support_esymm, Finset.mem_image] at hb2
  obtain ⟨I, hI, rfl⟩ := hb2
  have hIcard : I.card = s := (Finset.mem_powersetCard.mp hI).2
  have hadd : partitionVectorFinsupp (mu + Nat.PartitionVector.Pieri.prefixOnes s) =
      partitionVectorFinsupp mu +
        partitionVectorFinsupp (Nat.PartitionVector.Pieri.prefixOnes (N := N) s) := by
    ext j
    simp
  rw [← hsum, hadd, toLex_add, toLex_add]
  have h2 := toLex_sum_single_le_prefixOnes (N := N) I
  rw [hIcard] at h2
  exact add_le_add (toLex_le_of_mem_support_macdonaldP hb1) h2

/-! ### Separation by lower evaluations -/

/-- The two descriptions of the grid agree. -/
theorem grid_eq_pieriGrid (mu : Nat.PartitionVector N) :
    PartitionDivision.Macdonald.grid (macdonaldParamQ : 𝕂) macdonaldParamT mu =
      pieriGrid mu := by
  funext i
  simp only [PartitionDivision.Macdonald.grid, Nat.PartitionVector.Macdonald.grid,
    Nat.PartitionVector.staircase, Fin.val_rev]
  congr 2
  lia

/-- **Separation.**  On a lexicographically lower-closed finite set of partition vectors, the
evaluations of the Macdonald polynomials at the corresponding grids separate coefficient
vectors. -/
theorem separatesOn_pieriData {L : Finset (Nat.PartitionVector N)}
    (hL : IsLexLowerClosed (L : Set (Nat.PartitionVector N))) :
    (pieriData (N := N)).SeparatesOn L := by
  classical
  intro a b hab nu hnu
  set c : Nat.PartitionVector N → 𝕂 := fun kappa ↦ a kappa - b kappa with hc
  set F : MvPolynomial (Fin N) 𝕂 := ∑ kappa ∈ L, c kappa • macdonaldP kappa with hF
  have hFeval : ∀ pi ∈ L, eval (pieriGrid pi) F = 0 := by
    intro pi hpi
    have h := hab pi hpi
    simp only [pieriData_eval] at h
    change ∑ kappa ∈ L, a kappa * eval (pieriGrid pi) (macdonaldP kappa) =
      ∑ kappa ∈ L, b kappa * eval (pieriGrid pi) (macdonaldP kappa) at h
    rw [hF, map_sum]
    simp only [hc, smul_eval, sub_mul, Finset.sum_sub_distrib, h, sub_self]
  have hFspan : F ∈ Submodule.span 𝕂 (msymmVec 𝕂 '' (L : Set (Nat.PartitionVector N))) := by
    rw [← span_macdonaldP_image_eq hL]
    exact Submodule.sum_mem _ fun kappa hkappa ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨kappa, hkappa, rfl⟩)
  obtain ⟨d, hd⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' 𝕂).mp hFspan
  have hdzero : ∀ kappa ∈ L, d kappa = 0 := by
    have hv := Matrix.eq_zero_of_mulVec_eq_zero
      (PartitionDivision.Macdonald.det_orbitSum_grid_fractionRing_ne_zero L)
      (v := fun kappa : L ↦ d kappa.1) (by
        funext pi
        have h := hFeval pi.1 pi.2
        rw [← hd, map_sum] at h
        simp only [smul_eval, eval_msymmVec_eq_orbitSum] at h
        change ∑ kappa : L, PartitionDivision.Macdonald.orbitSum kappa.1
            (PartitionDivision.Macdonald.grid (macdonaldParamQ : 𝕂) macdonaldParamT pi.1) *
              d kappa.1 = 0
        rw [← h, ← Finset.sum_coe_sort L]
        refine Finset.sum_congr rfl fun kappa _ ↦ ?_
        rw [grid_eq_pieriGrid, mul_comm])
    intro kappa hkappa
    exact congrFun hv ⟨kappa, hkappa⟩
  have hF0 : F = 0 := by
    rw [← hd]
    exact Finset.sum_eq_zero fun kappa hkappa ↦ by rw [hdzero kappa hkappa, zero_smul]
  have h := linearIndependent_iff'.mp linearIndependent_macdonaldP L c (hF ▸ hF0) nu hnu
  exact sub_eq_zero.mp h

/-! ### Normalization transfers -/

namespace EvaluationPieriData

variable {K A I S : Type*} [Field K] [CommRing A] [Algebra K A]
variable (D : EvaluationPieriData (K := K) (A := A) (I := I) (S := S))

/-- Separation survives normalization by nonzero base values. -/
theorem SeparatesOn.normalized {lower : Finset I} (h : D.SeparatesOn lower) (base : I)
    (hne : ∀ nu, D.eval base (D.p nu) ≠ 0) : (D.normalized base).SeparatesOn lower := by
  intro a b hab nu hnu
  have h' := h (fun nu ↦ a nu * (D.eval base (D.p nu))⁻¹)
    (fun nu ↦ b nu * (D.eval base (D.p nu))⁻¹) (by
      intro pi hpi
      have hpi' := hab pi hpi
      change ∑ nu ∈ lower, a nu * D.eval pi ((D.eval base (D.p nu))⁻¹ • D.p nu) =
        ∑ nu ∈ lower, b nu * D.eval pi ((D.eval base (D.p nu))⁻¹ • D.p nu) at hpi'
      simp only [map_smul, smul_eq_mul] at hpi'
      simpa only [mul_assoc] using hpi') nu hnu
  exact mul_right_cancel₀ (inv_ne_zero (hne nu)) h'

/-- A lower expansion survives normalization by nonzero base values. -/
theorem InSpanOn.normalized {lower : Finset I} {x : A} (h : D.InSpanOn lower x) (base : I)
    (hne : ∀ nu, D.eval base (D.p nu) ≠ 0) : (D.normalized base).InSpanOn lower x := by
  refine (Submodule.span_le.mpr ?_) h
  rintro _ ⟨nu, hnu, rfl⟩
  have hp : D.p nu = D.eval base (D.p nu) • D.normalizeAt base nu := by
    rw [normalizeAt, smul_smul, mul_inv_cancel₀ (hne nu), one_smul]
  rw [SetLike.mem_coe, hp]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨nu, hnu, rfl⟩)

/-- The product of a normalized member with a multiplier stays in a span when the raw product
does. -/
theorem InSpanOn.normalizeAt_mul {lower : Finset I} {mu : I} {s : S}
    (h : D.InSpanOn lower (D.p mu * D.elem s)) (base : I)
    (hne : ∀ nu, D.eval base (D.p nu) ≠ 0) :
    (D.normalized base).InSpanOn lower (D.normalizeAt base mu * D.elem s) := by
  have h' := InSpanOn.normalized D h base hne
  rw [normalizeAt, smul_mul_assoc]
  exact Submodule.smul_mem _ _ h'

end EvaluationPieriData

/-! ### The grid recurrence in the form of the abstract induction -/

/-- The sum over row subsets in the grid recurrence is the sum over strip successors. -/
theorem sum_gridRecurrenceTerm_eq (mu : Nat.PartitionVector N) (s : ℕ)
    (f : MvPolynomial (Fin N) 𝕂) :
    ∑ I ∈ Finset.univ.powersetCard s,
        Nat.PartitionVector.Macdonald.gridRecurrenceTerm macdonaldParamQ macdonaldParamT mu f I =
      ∑ nu ∈ stripSuccessors mu s, stripCoeff mu s nu * eval (pieriGrid nu) f := by
  classical
  rw [stripSuccessors, Finset.sum_image]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ ↦ ?_
    by_cases hI : Nat.PartitionVector.Macdonald.IsLegal mu I
    · rw [addStrip_of_isLegal hI, stripCoeff, filter_lt_incrementPartition]
      simp [Nat.PartitionVector.Macdonald.gridRecurrenceTerm, hI]
    · simp [Nat.PartitionVector.Macdonald.gridRecurrenceTerm, hI]
  · intro I hI J hJ hIJ
    have hI' := (Finset.mem_filter.mp hI).2
    have hJ' := (Finset.mem_filter.mp hJ).2
    rw [Finset.mem_coe] at hI hJ
    rw [addStrip_of_isLegal hI', addStrip_of_isLegal hJ'] at hIJ
    ext i
    have h := congrArg (fun nu : Nat.PartitionVector N ↦ nu i) hIJ
    simp only [Nat.PartitionVector.Macdonald.incrementPartition_apply] at h
    by_cases hiI : i ∈ I <;> by_cases hiJ : i ∈ J <;> simp_all

/-- The grid recurrence for `macdonaldP`, in the form of ledger Lemma 10: for every `λ`, `μ` and
`r`, `ε_r(λ) u_μ(P_λ) = Σ_{|I| = r} B_{μ,I} u_{μ + 1_I}(P_λ)`, with illegal `I` omitted.  It
follows from the eigenvalue equation `D^r P_λ = ε_r(λ) P_λ` (ledger Lemma 7) by
`gridRecurrence_of_vandermondeRatio`; it is a hypothesis here. -/
def MacdonaldGridRecurrence : Prop :=
  ∀ (lambda mu : Nat.PartitionVector N) (r : ℕ),
    macdonaldEigenvalueR macdonaldParamQ macdonaldParamT r lambda *
        eval (pieriGrid mu) (macdonaldP lambda) =
      ∑ I ∈ Finset.univ.powersetCard r,
        Nat.PartitionVector.Macdonald.gridRecurrenceTerm macdonaldParamQ macdonaldParamT mu
          (macdonaldP lambda) I

/-- The ledger Lemma 10 recurrence gives the abstract grid recurrence. -/
theorem hasGridRecurrence_pieriData (hrec : MacdonaldGridRecurrence (N := N)) :
    (pieriData (N := N)).HasGridRecurrence := by
  intro lambda mu s
  simp only [pieriData_eval]
  change eval (pieriGrid lambda) (esymm (Fin N) 𝕂 s) *
      eval (pieriGrid mu) (macdonaldP lambda) =
    ∑ nu ∈ stripSuccessors mu s, stripCoeff mu s nu * eval (pieriGrid nu) (macdonaldP lambda)
  rw [eval_esymm_pieriGrid, hrec lambda mu s, sum_gridRecurrenceTerm_eq]

/-- The joint spectral action of the Macdonald operators on `macdonaldP` (ledger Lemma 7, eq.
(5.1)), in numerator form: `vandermonde * D^r P_λ = ε_r(λ) vandermonde P_λ` for every `r`.  By
`macdonaldOp_eq_smul_iff` this is the eigenvalue equation `D^r P_λ = ε_r(λ) P_λ`. -/
def MacdonaldJointEigen : Prop :=
  ∀ (lambda : Nat.PartitionVector N) (r : ℕ),
    macdonaldOpNumerator macdonaldParamQ macdonaldParamT r (macdonaldP lambda) =
      macdonaldEigenvalueR macdonaldParamQ macdonaldParamT r lambda •
        (vandermonde N 𝕂 * macdonaldP lambda)

/-- Ledger Lemma 10 for `macdonaldP`: the joint spectral action gives the grid recurrence. -/
theorem macdonaldGridRecurrence_of_jointEigen (h : MacdonaldJointEigen (N := N)) :
    MacdonaldGridRecurrence (N := N) := by
  intro lambda mu r
  refine Nat.PartitionVector.Macdonald.gridRecurrence_of_vandermondeRatio
    powerPairInjective_macdonaldParam mu r (macdonaldP lambda)
    (macdonaldEigenvalueR macdonaldParamQ macdonaldParamT r lambda • macdonaldP lambda)
    ?_ rfl
  rw [mul_smul_comm, ← h lambda r]
  rfl

/-! ### The main theorem -/

/-- The Macdonald polynomial normalized to take the value one at the base grid
`(t ^ (N - 1), …, t, 1)`. -/
def macdonaldPNormalized (mu : Nat.PartitionVector N) : MvPolynomial (Fin N) 𝕂 :=
  (eval (pieriGrid 0) (macdonaldP mu))⁻¹ • macdonaldP mu

/-- **Evaluation symmetry and normalized Pieri** (Macdonald VI (6.6)--(6.8), Pieri ledger
Lemma 12, equations (5.3) and (5.4)), conditional on the grid recurrence (ledger Lemma 10, which
depends on Lemma 7) and on the nonvanishing of the base evaluations (ledger Lemma 8).

With `P̄_μ = P_μ / u_0(P_μ)`:
* `u_0(P̄_μ) = 1`;
* `u_λ(P̄_μ) = u_μ(P̄_λ)`;
* `P̄_μ e_s = Σ_{ν = μ + 1_I legal, #I = s} B_{μ,I} P̄_ν`. -/
theorem macdonaldP_normalized_symmetry_and_pieri (hrec : MacdonaldGridRecurrence (N := N))
    (hne : ∀ lambda : Nat.PartitionVector N, eval (pieriGrid 0) (macdonaldP lambda) ≠ 0) :
    (∀ mu : Nat.PartitionVector N, eval (pieriGrid 0) (macdonaldPNormalized mu) = 1) ∧
      (∀ lambda mu : Nat.PartitionVector N,
        eval (pieriGrid lambda) (macdonaldPNormalized mu) =
          eval (pieriGrid mu) (macdonaldPNormalized lambda)) ∧
      ∀ (mu : Nat.PartitionVector N) (s : ℕ),
        macdonaldPNormalized mu * esymm (Fin N) 𝕂 s =
          ∑ nu ∈ stripSuccessors mu s, stripCoeff mu s nu • macdonaldPNormalized nu := by
  have hne' : ∀ mu, (pieriData (N := N)).eval 0 ((pieriData (N := N)).p mu) ≠ 0 := by
    intro mu
    change (pieriData.eval 0) (macdonaldP mu) ≠ 0
    simpa using hne mu
  have hexpandPS : ∀ mu s, (pieriData (N := N)).InSpanOn (lowerPS mu s)
      ((pieriData (N := N)).p mu * (pieriData (N := N)).elem s) :=
    fun mu s ↦ macdonaldP_mul_esymm_mem_span mu s
  have hsepPS : ∀ mu s, (pieriData (N := N)).SeparatesOn (lowerPS mu s) :=
    fun mu s ↦ separatesOn_pieriData (isLexLowerClosed_lexLowerFinset _ _)
  have h := (pieriData (N := N)).normalized_symmetry_and_pieri SizeLexLT wellFounded_sizeLexLT 0
    lowerTop removeColumn numParts lowerPS macdonaldP_zero hne'
    (hasGridRecurrence_pieriData hrec)
    (fun h ↦ eq_or_sizeLexLT_of_mem_lowerTop h)
    (fun mu hmu ↦ sizeLexLT_removeColumn hmu)
    (fun mu _ ↦ mem_stripSuccessors_removeColumn mu)
    (fun mu _ ↦ by
      rw [← lowerPS_removeColumn]
      exact stripSuccessors_subset_lowerPS _ _)
    (fun mu _ ↦ stripCoeff_removeColumn_ne_zero mu)
    (fun mu _ ↦ by
      rw [← lowerPS_removeColumn]
      exact EvaluationPieriData.SeparatesOn.normalized _ (hsepPS _ _) 0 hne')
    (fun mu _ ↦ by
      rw [← lowerPS_removeColumn]
      exact EvaluationPieriData.InSpanOn.normalizeAt_mul _ (hexpandPS _ _) 0 hne')
    stripSuccessors_subset_lowerPS
    (fun mu s ↦ EvaluationPieriData.SeparatesOn.normalized _ (hsepPS mu s) 0 hne')
    (fun mu s ↦ EvaluationPieriData.InSpanOn.normalizeAt_mul _ (hexpandPS mu s) 0 hne')
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun mu ↦ ?_, fun lambda mu ↦ ?_, fun mu s ↦ ?_⟩
  · simpa [EvaluationPieriData.normalizeAt, macdonaldPNormalized, pieriData] using h1 mu
  · simpa [EvaluationPieriData.normalizeAt, macdonaldPNormalized, pieriData] using h2 lambda mu
  · simpa [EvaluationPieriData.normalizeAt, macdonaldPNormalized, pieriData] using h3 mu s

/-- Ledger Lemma 12 for `macdonaldP`, conditional only on the joint spectral action (Lemma 7) and
the nonvanishing base evaluations (Lemma 8). -/
theorem macdonaldP_normalized_symmetry_and_pieri_of_jointEigen
    (heig : MacdonaldJointEigen (N := N))
    (hne : ∀ lambda : Nat.PartitionVector N, eval (pieriGrid 0) (macdonaldP lambda) ≠ 0) :
    (∀ mu : Nat.PartitionVector N, eval (pieriGrid 0) (macdonaldPNormalized mu) = 1) ∧
      (∀ lambda mu : Nat.PartitionVector N,
        eval (pieriGrid lambda) (macdonaldPNormalized mu) =
          eval (pieriGrid mu) (macdonaldPNormalized lambda)) ∧
      ∀ (mu : Nat.PartitionVector N) (s : ℕ),
        macdonaldPNormalized mu * esymm (Fin N) 𝕂 s =
          ∑ nu ∈ stripSuccessors mu s, stripCoeff mu s nu • macdonaldPNormalized nu :=
  macdonaldP_normalized_symmetry_and_pieri (macdonaldGridRecurrence_of_jointEigen heig) hne

end Macdonald
