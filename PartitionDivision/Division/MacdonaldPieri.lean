/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Division.Specialization
public import PartitionDivision.Macdonald.PieriInduction
public import PartitionDivision.Macdonald.PrincipalSpecialization

/-!
# The generic vertical Pieri rule for the Macdonald polynomials

This file assembles Pieri ledger Lemma 15 for `MvPolynomial.macdonaldP` over `ℚ(q, t)`:
`SatisfiesPolynomialPieri macdonaldP macdonaldParamQ macdonaldParamT`.  It is conditional on two
explicit hypotheses, proved elsewhere:

* (L7) `Macdonald.MacdonaldJointEigen`, the joint eigenvalue equation `D^r P_λ = ε_r(λ) P_λ`;
* (L8) `u_0(P_λ) ≠ 0`, where `u_0` is evaluation at `(t ^ (N - 1), …, t, 1)`.

The steps are:

1. **Principal specialization** (Lemma 13): `u_0(P_λ) = principalSpecialization q t λ`.  This is
   proved by induction on the first-column decomposition, comparing the coefficients of the
   leading exponent `λ` in the normalized Pieri identity (5.4) for `μ = removeColumn λ` and the
   prefix strip, and then using `principalSpecialization_incrementPrefix`.
2. **Unnormalization** (Lemma 14): `e_s P_μ = Σ B_{μ,I} u_0(P_μ) / u_0(P_{μ+1_I}) P_{μ+1_I}`,
   and `principalSpecialization_pieriCancellation` turns each coefficient into the row-pair
   ratio `pieriNum / pieriDen`.
3. **Encodings**: row subsets are converted to zero-one strips with `stripOfFinset`, matching
   `IsLegal`, `addStrip` and `stripWeight` of `PartitionDivision.Division.Factorization`.
-/

@[expose] public section

noncomputable section

open Finset
open scoped MonomialOrder

/-- The field `ℚ(q, t)` of rational functions in the Macdonald parameters. -/
local notation "𝕂" => FractionRing (MvPolynomial (Fin 2) ℚ)

namespace Nat.PartitionVector.Macdonald

variable {N : ℕ} {K : Type*}

/-- The principal specialization of the empty partition is one. -/
theorem principalSpecialization_zero [Field K] (q t : K) :
    principalSpecialization q t (0 : Nat.PartitionVector N) = 1 := by
  simp [principalSpecialization, nStatistic, principalRowFactor,
    Nat.PartitionVector.Pieri.rowDifference, specializationPochhammer]

end Nat.PartitionVector.Macdonald

namespace Macdonald

open MvPolynomial

variable {N : ℕ}

/-! ### Leading coefficients -/

/-- The indicator exponent of the first `s` rows. -/
theorem partitionVectorFinsupp_prefixOnes (s : ℕ) :
    partitionVectorFinsupp (Nat.PartitionVector.Pieri.prefixOnes (N := N) s) =
      ∑ i ∈ Nat.PartitionVector.Macdonald.prefixRows N s, Finsupp.single i 1 := by
  classical
  ext j
  simp [Finsupp.single_apply]

/-- A row subset is recovered from its indicator exponent. -/
theorem sum_single_injective :
    Function.Injective fun I : Finset (Fin N) ↦ ∑ i ∈ I, Finsupp.single i (1 : ℕ) := by
  classical
  intro I J h
  ext j
  have hj := congrArg (fun d : Fin N →₀ ℕ ↦ d j) h
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq'] at hj
  by_cases hI : j ∈ I <;> by_cases hJ : j ∈ J <;> simp_all

/-- The coefficient of `esymm s` at the indicator of the first `s` rows is one. -/
theorem coeff_esymm_prefixOnes {s : ℕ} (hs : s ≤ N) :
    (esymm (Fin N) 𝕂 s).coeff
      (partitionVectorFinsupp (Nat.PartitionVector.Pieri.prefixOnes (N := N) s)) = 1 := by
  classical
  have hmem : Nat.PartitionVector.Macdonald.prefixRows N s ∈
      (Finset.univ : Finset (Fin N)).powersetCard s := by
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Nat.PartitionVector.Macdonald.prefixRows, Fin.card_filter_val_lt]
    exact min_eq_right hs
  rw [esymm_eq_sum_monomial, coeff_sum, partitionVectorFinsupp_prefixOnes,
    Finset.sum_eq_single (Nat.PartitionVector.Macdonald.prefixRows N s)]
  · simp
  · intro I _ hI
    rw [coeff_monomial]
    split_ifs with h
    · exact absurd (sum_single_injective h) hI
    · rfl
  · intro h
    exact absurd hmem h

/-- The coefficient of `P_μ e_s` at `μ + 1 ^ s` is one, for `s ≤ N`. -/
theorem coeff_macdonaldP_mul_esymm {s : ℕ} (hs : s ≤ N) (mu : Nat.PartitionVector N) :
    (macdonaldP mu * esymm (Fin N) 𝕂 s).coeff
      (partitionVectorFinsupp mu +
        partitionVectorFinsupp (Nat.PartitionVector.Pieri.prefixOnes (N := N) s)) = 1 := by
  classical
  have ha : MonomialOrder.lex.degree (macdonaldP mu) ≼[MonomialOrder.lex]
      partitionVectorFinsupp mu := by
    rw [MonomialOrder.degree_le_iff]
    intro b hb
    exact toLex_le_of_mem_support_macdonaldP hb
  have hb : MonomialOrder.lex.degree (esymm (Fin N) 𝕂 s) ≼[MonomialOrder.lex]
      partitionVectorFinsupp (Nat.PartitionVector.Pieri.prefixOnes (N := N) s) := by
    rw [MonomialOrder.degree_le_iff]
    intro b hb
    rw [support_esymm, Finset.mem_image] at hb
    obtain ⟨I, hI, rfl⟩ := hb
    have h := toLex_sum_single_le_prefixOnes (N := N) I
    rwa [(Finset.mem_powersetCard.mp hI).2] at h
  rw [MonomialOrder.coeff_mul_of_add_of_degree_le ha hb, coeff_macdonaldP_self,
    coeff_esymm_prefixOnes hs, one_mul]

/-- A Macdonald polynomial indexed lexicographically at most `λ` has coefficient `[ν = λ]` at
`λ`. -/
theorem coeff_macdonaldP_of_toLex_le {nu lam : Nat.PartitionVector N}
    (h : toLex (partitionVectorFinsupp nu) ≤ toLex (partitionVectorFinsupp lam)) :
    (macdonaldP nu).coeff (partitionVectorFinsupp lam) = if nu = lam then 1 else 0 := by
  split_ifs with heq
  · subst heq
    exact coeff_macdonaldP_self nu
  · have hlt : toLex (partitionVectorFinsupp nu) < toLex (partitionVectorFinsupp lam) :=
      lt_of_le_of_ne h fun h' ↦ heq (partitionVectorFinsupp_injective (toLex.injective h'))
    by_contra hne
    have hle := toLex_le_of_mem_support_macdonaldP (mem_support_iff.mpr hne)
    exact lt_irrefl _ (hle.trans_lt hlt)

/-! ### Sums over strip successors -/

open Classical in
/-- A sum over strip successors is a sum over legal row subsets. -/
theorem sum_stripSuccessors {M : Type*} [AddCommMonoid M] (mu : Nat.PartitionVector N) (s : ℕ)
    (F : Nat.PartitionVector N → M) :
    ∑ nu ∈ stripSuccessors mu s, F nu =
      ∑ I ∈ (Finset.univ.powersetCard s).filter
          (fun I ↦ Nat.PartitionVector.Macdonald.IsLegal mu I),
        F (addStrip mu I) := by
  rw [stripSuccessors, Finset.sum_image]
  intro I hI J hJ hIJ
  have hI' := (Finset.mem_filter.mp hI).2
  have hJ' := (Finset.mem_filter.mp hJ).2
  rw [addStrip_of_isLegal hI', addStrip_of_isLegal hJ'] at hIJ
  ext i
  have h := congrArg (fun nu : Nat.PartitionVector N ↦ nu i) hIJ
  simp only [Nat.PartitionVector.Macdonald.incrementPartition_apply] at h
  by_cases hiI : i ∈ I <;> by_cases hiJ : i ∈ J <;> simp_all

/-! ### Principal specialization -/

/-- Removing the first column and adding back the prefix strip is `incrementPrefix`. -/
theorem incrementPrefix_removeColumn (lam : Nat.PartitionVector N) :
    Nat.PartitionVector.Macdonald.incrementPrefix (removeColumn lam) (numParts lam) = lam := by
  apply Nat.PartitionVector.ext
  intro i
  rw [Nat.PartitionVector.Macdonald.incrementPrefix_apply]
  have h := congrArg (fun nu : Nat.PartitionVector N ↦ nu i) (removeColumn_add_prefixOnes lam)
  simpa using h

/-- The coefficient of the first-column successor is the prefix grid coefficient. -/
theorem stripCoeff_removeColumn (lam : Nat.PartitionVector N) :
    stripCoeff (removeColumn lam) (numParts lam) lam =
      Nat.PartitionVector.Macdonald.B macdonaldParamQ macdonaldParamT (removeColumn lam)
        (Nat.PartitionVector.Macdonald.prefixRows N (numParts lam)) := by
  rw [stripCoeff]
  congr 1
  ext i
  rw [Finset.mem_filter, Nat.PartitionVector.Macdonald.mem_prefixRows, lt_numParts_iff]
  simp only [Finset.mem_univ, true_and, removeColumn_apply]
  lia

/-- **Principal specialization** (Pieri ledger Lemma 13).  Under the joint spectral action and
the nonvanishing of the base evaluations, `u_0(P_λ) = Φ(λ)`. -/
theorem eval_pieriGrid_zero_macdonaldP (heig : MacdonaldJointEigen (N := N))
    (hne : ∀ lam : Nat.PartitionVector N, eval (pieriGrid 0) (macdonaldP lam) ≠ 0)
    (lam : Nat.PartitionVector N) :
    eval (pieriGrid 0) (macdonaldP lam) =
      Nat.PartitionVector.Macdonald.principalSpecialization macdonaldParamQ macdonaldParamT
        lam := by
  have hpieri := (macdonaldP_normalized_symmetry_and_pieri_of_jointEigen heig hne).2.2
  induction lam using (wellFounded_sizeLexLT (N := N)).induction with
  | h lam ih =>
    by_cases hlam : lam = 0
    · subst hlam
      rw [macdonaldP_zero, map_one, Nat.PartitionVector.Macdonald.principalSpecialization_zero]
    set mu := removeColumn lam with hmu
    set s := numParts lam with hs
    have hsN : s ≤ N := by
      have h := Finset.card_le_univ (Finset.univ.filter fun i : Fin N ↦ 0 < lam i)
      simpa [hs, numParts] using h
    have hlamD : partitionVectorFinsupp lam = partitionVectorFinsupp mu +
        partitionVectorFinsupp (Nat.PartitionVector.Pieri.prefixOnes (N := N) s) := by
      rw [← removeColumn_add_prefixOnes lam]
      ext j
      simp [hmu, hs]
    have hc := congrArg (fun p : MvPolynomial (Fin N) 𝕂 ↦ p.coeff (partitionVectorFinsupp lam))
      (hpieri mu s)
    simp only [macdonaldPNormalized, smul_mul_assoc, coeff_smul, coeff_sum, smul_eq_mul] at hc
    rw [hlamD, coeff_macdonaldP_mul_esymm hsN, ← hlamD, mul_one,
      Finset.sum_eq_single lam] at hc
    · rw [coeff_macdonaldP_self, mul_one, stripCoeff_removeColumn] at hc
      have hmu0 := ih mu (sizeLexLT_removeColumn hlam)
      have hspec := Nat.PartitionVector.Macdonald.principalSpecialization_incrementPrefix
        powerPairInjective_macdonaldParam mu s
      rw [incrementPrefix_removeColumn] at hspec
      rw [hspec, ← hmu0]
      have h1 := hne mu
      have h2 := hne lam
      field_simp at hc
      linear_combination hc
    · intro nu hnu hnulam
      have hle : toLex (partitionVectorFinsupp nu) ≤ toLex (partitionVectorFinsupp lam) := by
        have h := stripSuccessors_subset_lowerPS mu s hnu
        rw [hmu, hs, lowerPS_removeColumn, lowerTop, mem_lexLowerFinset] at h
        exact h.2
      rw [coeff_macdonaldP_of_toLex_le hle]
      simp [hnulam]
    · intro h
      exact absurd (mem_stripSuccessors_removeColumn lam) h

/-! ### The unnormalized Pieri rule -/

open Classical in
/-- **Unnormalized Pieri rule over row subsets.**  With
`c(I) = B_{μ,I} Φ(μ) / Φ(μ + 1_I)`, `e_s P_μ = Σ_{I legal, #I = s} c(I) P_{μ + 1_I}`. -/
theorem esymm_mul_macdonaldP_eq_sum (heig : MacdonaldJointEigen (N := N))
    (hne : ∀ lam : Nat.PartitionVector N, eval (pieriGrid 0) (macdonaldP lam) ≠ 0)
    (mu : Nat.PartitionVector N) (s : ℕ) :
    esymm (Fin N) 𝕂 s * macdonaldP mu =
      ∑ I ∈ (Finset.univ.powersetCard s).filter
          (fun I ↦ Nat.PartitionVector.Macdonald.IsLegal mu I),
        (Nat.PartitionVector.Macdonald.B macdonaldParamQ macdonaldParamT mu I *
            eval (pieriGrid 0) (macdonaldP mu) /
              eval (pieriGrid 0) (macdonaldP (addStrip mu I))) •
          macdonaldP (addStrip mu I) := by
  have hpieri := (macdonaldP_normalized_symmetry_and_pieri_of_jointEigen heig hne).2.2 mu s
  rw [sum_stripSuccessors] at hpieri
  have hmu := hne mu
  calc
    esymm (Fin N) 𝕂 s * macdonaldP mu =
        eval (pieriGrid 0) (macdonaldP mu) • (macdonaldPNormalized mu * esymm (Fin N) 𝕂 s) := by
      rw [macdonaldPNormalized, smul_mul_assoc, smul_smul, mul_inv_cancel₀ hmu, one_smul,
        mul_comm]
    _ = _ := by
      rw [hpieri, Finset.smul_sum]
      refine Finset.sum_congr rfl fun I hI ↦ ?_
      have hI' := (Finset.mem_filter.mp hI).2
      rw [macdonaldPNormalized, smul_smul, smul_smul, addStrip_of_isLegal hI', stripCoeff,
        filter_lt_incrementPartition]
      congr 1
      ring

/-- The successor `addStrip μ I` of the subset encoding is the successor of its zero-one strip. -/
theorem addStrip_stripOfFinset {mu : Nat.PartitionVector N} {I : Finset (Fin N)}
    (hI : Nat.PartitionVector.Macdonald.IsLegal mu I) :
    PartitionDivision.addStrip mu (Nat.PartitionVector.Macdonald.stripOfFinset I) =
      addStrip mu I := by
  have hI' : Nat.PartitionVector.Pieri.IsLegal mu
      (Nat.PartitionVector.Macdonald.stripOfFinset I) :=
    (Nat.PartitionVector.Macdonald.isLegal_stripOfFinset_iff mu I).mpr hI
  apply Nat.PartitionVector.ext
  intro i
  rw [PartitionDivision.addStrip_apply_of_legal hI', addStrip_of_isLegal hI,
    Nat.PartitionVector.Macdonald.incrementPartition_apply]
  by_cases hi : i ∈ I <;> simp [Nat.PartitionVector.Macdonald.stripOfFinset, hi]

/-- The weight of the strip of a row subset is its cardinality. -/
theorem stripWeight_stripOfFinset (I : Finset (Fin N)) :
    PartitionDivision.stripWeight (Nat.PartitionVector.Macdonald.stripOfFinset I) = I.card := by
  have h (i : Fin N) :
      ((Nat.PartitionVector.Macdonald.stripOfFinset I i : Fin 2) : ℕ) =
        if i ∈ I then 1 else 0 := by
    by_cases hi : i ∈ I <;> simp [Nat.PartitionVector.Macdonald.stripOfFinset, hi]
  simp only [PartitionDivision.stripWeight, h, Finset.sum_boole, Nat.cast_id]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- The rows on which a zero-one strip is one. -/
def finsetOfStrip (delta : Nat.PartitionVector.Pieri.Strip N) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ delta i = 1

/-- A zero-one strip is the strip of the rows on which it is one. -/
theorem stripOfFinset_finsetOfStrip (delta : Nat.PartitionVector.Pieri.Strip N) :
    Nat.PartitionVector.Macdonald.stripOfFinset (finsetOfStrip delta) = delta := by
  funext i
  simp only [Nat.PartitionVector.Macdonald.stripOfFinset, finsetOfStrip, Finset.mem_filter,
    Finset.mem_univ, true_and]
  split_ifs with h
  · exact h.symm
  · have hx : ∀ x : Fin 2, x ≠ 1 → 0 = x := by decide
    exact hx _ h

/-- The rows of the strip of a row subset are that subset. -/
theorem finsetOfStrip_stripOfFinset (I : Finset (Fin N)) :
    finsetOfStrip (Nat.PartitionVector.Macdonald.stripOfFinset I) = I := by
  ext i
  simp [finsetOfStrip]

open Classical in
/-- A sum over legal row subsets of size `s` is a sum over legal zero-one strips of weight
`s`. -/
theorem sum_legal_finset_eq_sum_strip {M : Type*} [AddCommMonoid M]
    (mu : Nat.PartitionVector N) (s : ℕ) (G : Nat.PartitionVector.Pieri.Strip N → M) :
    ∑ I ∈ (Finset.univ.powersetCard s).filter
        (fun I ↦ Nat.PartitionVector.Macdonald.IsLegal mu I),
      G (Nat.PartitionVector.Macdonald.stripOfFinset I) =
    ∑ delta : Nat.PartitionVector.Pieri.Strip N,
      if Nat.PartitionVector.Pieri.IsLegal mu delta ∧ PartitionDivision.stripWeight delta = s
      then G delta else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' Nat.PartitionVector.Macdonald.stripOfFinset finsetOfStrip
    ?_ ?_ ?_ ?_ ?_
  · intro I hI
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hI
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      (Nat.PartitionVector.Macdonald.isLegal_stripOfFinset_iff mu I).mpr hI.2,
      (stripWeight_stripOfFinset I).trans hI.1.2⟩
  · intro delta hdelta
    rw [Finset.mem_filter] at hdelta
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    have hd := stripOfFinset_finsetOfStrip delta
    refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · rw [← stripWeight_stripOfFinset, hd]
      exact hdelta.2.2
    · rw [← Nat.PartitionVector.Macdonald.isLegal_stripOfFinset_iff, hd]
      exact hdelta.2.1
  · intro I _
    exact finsetOfStrip_stripOfFinset I
  · intro delta _
    exact stripOfFinset_finsetOfStrip delta
  · intro I _
    rfl

end Macdonald

namespace PartitionDivision

open MvPolynomial

variable {N : ℕ}

/-- **The generic vertical Pieri rule for the Macdonald polynomials** (Pieri ledger Lemma 15),
conditional on the joint spectral action (Lemma 7, `MacdonaldJointEigen`) and on the
nonvanishing of the base evaluations (Lemma 8). -/
theorem satisfiesPolynomialPieri_macdonaldP (heig : Macdonald.MacdonaldJointEigen (N := N))
    (hne : ∀ lam : Nat.PartitionVector N,
      eval (Macdonald.pieriGrid 0) (macdonaldP lam) ≠ 0) :
    SatisfiesPolynomialPieri (macdonaldP : Nat.PartitionVector N → MvPolynomial (Fin N) 𝕂)
      macdonaldParamQ macdonaldParamT := by
  classical
  intro r lam
  rw [Macdonald.esymm_mul_macdonaldP_eq_sum heig hne lam r]
  rw [← Macdonald.sum_legal_finset_eq_sum_strip lam r
    (fun delta ↦ pieriCoefficient macdonaldParamQ macdonaldParamT lam delta •
      macdonaldP (addStrip lam delta))]
  refine Finset.sum_congr rfl fun I hI ↦ ?_
  have hI' := (Finset.mem_filter.mp hI).2
  rw [Macdonald.addStrip_stripOfFinset hI', Macdonald.addStrip_of_isLegal hI',
    Macdonald.eval_pieriGrid_zero_macdonaldP heig hne,
    Macdonald.eval_pieriGrid_zero_macdonaldP heig hne, pieriCoefficient,
    Nat.PartitionVector.Macdonald.principalSpecialization_pieriCancellation
      Macdonald.powerPairInjective_macdonaldParam lam I hI']

end PartitionDivision
