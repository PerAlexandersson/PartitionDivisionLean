/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Division.Specialization
public import PartitionDivision.Macdonald.BasicLexUnitriangular
public import PartitionDivision.Macdonald.DiagonalSpecialization
public import PartitionDivision.Macdonald.SchurPrincipal
public import PartitionDivision.TauCeti.Combinatorics.Young.VerticalStrip

/-!
# The specialization `q = t` and the nonvanishing of `u_0(P_λ)`

This file proves Pieri ledger Lemma 8 (`docs/PIERI.md`) for every family satisfying the
hypotheses (U) and (P) of `PartitionDivision.Division.Specialization`.

* `pieriCoefficient_self_eq_one`: `ψ'(t, t) = 1` for every legal strip.
* `esymm_mul_schurVec`, `satisfiesPolynomialPieri_schurVec`: the Schur polynomials satisfy the
  vertical Pieri rule with all coefficients one, written with `Strip`, `IsLegal` and `addStrip`.
  The proof goes through the bialternant formula and Tau Ceti's `esymm_mul_alternant`.
* `eq_of_satisfiesPolynomialPieri`: a family satisfying a vertical Pieri rule is determined by its
  value at the empty partition.  Removing the first column of `λ` and adding it back is the
  lexicographically largest Pieri step, and its coefficient is one.
* `coe_specializedBasis_diagonal`: at `q = t` the specialized basis is the Schur basis.
* `eval_staircase_ne_zero`: **Lemma 8**, `P_λ(t ^ (N - 1), …, t, 1) ≠ 0` in `ℚ(q, t)`.
* `eval_grid_zero_macdonaldP_ne_zero`: Lemma 8 for `MvPolynomial.macdonaldP`, conditional on the
  generic Pieri rule for the Macdonald polynomials, which is kept as an explicit hypothesis.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Polynomial

namespace PartitionDivision

open MvPolynomial Nat.PartitionVector Nat.PartitionVector.Pieri Macdonald TauCeti

attribute [local instance] RingHom.ker_isPrime

variable {N : ℕ}

/-- **`ψ'(t, t) = 1`.**  At `q = t` the Pieri coefficient of every legal strip is one, as soon as
no positive power of `t` is one. -/
theorem pieriCoefficient_self_eq_one {F : Type*} [Field F] {t : F}
    (ht : ∀ n : ℕ, n ≠ 0 → t ^ n ≠ 1) {lam : Nat.PartitionVector N} {δ : Strip N}
    (hδ : IsLegal lam δ) : pieriCoefficient t t lam δ = 1 := by
  rw [pieriCoefficient, pieriNum_self_eq_pieriDen t hδ]
  exact div_self (pieriDen_self_ne_zero ht lam δ)

/-! ### Strips and finite sets of rows -/

/-- Zero-one strips are the indicator functions of finite sets of rows. -/
def stripEquivFinset : Strip N ≃ Finset (Fin N) where
  toFun δ := Finset.univ.filter fun i ↦ δ i = 1
  invFun T i := if i ∈ T then 1 else 0
  left_inv δ := by
    funext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · exact h.symm
    · exact (Fin.eq_zero_or_eq_succ (δ i)).elim Eq.symm fun ⟨j, hj⟩ ↦ by
        exfalso
        apply h
        rw [hj, Fin.fin_one_eq_zero j]
        rfl
  right_inv T := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h <;> simp [h]

/-- The value of a strip is the indicator of its set of rows. -/
theorem val_strip_eq_ite (δ : Strip N) (i : Fin N) :
    ((δ i : Fin 2) : ℕ) = if i ∈ stripEquivFinset δ then 1 else 0 := by
  have h := congrFun (stripEquivFinset.left_inv δ) i
  conv_lhs => rw [← h]
  change ((if i ∈ stripEquivFinset δ then 1 else 0 : Fin 2) : ℕ) = _
  split_ifs <;> rfl

/-- The weight of a strip is the number of its rows. -/
theorem stripWeight_eq_card (δ : Strip N) : stripWeight δ = (stripEquivFinset δ).card := by
  rw [stripWeight]
  simp_rw [val_strip_eq_ite]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.card_eq_sum_ones]

/-! ### The Schur Pieri rule in strip form -/

/-- A strip whose shifted staircase exponents stay pairwise distinct is legal. -/
theorem isLegal_of_injective {lam : Nat.PartitionVector N} {δ : Strip N}
    (h : Function.Injective fun j : Fin N ↦ lam j + (N - 1 - j) + (δ j : ℕ)) :
    IsLegal lam δ := by
  have hβ : (fun j : Fin N ↦ (youngDiagram lam).betaNumber N j +
      if j ∈ stripEquivFinset δ then 1 else 0) =
      fun j : Fin N ↦ lam j + (N - 1 - j) + (δ j : ℕ) := by
    funext j
    rw [YoungDiagram.betaNumber_def, rowLen_youngDiagram, val_strip_eq_ite]
  have hanti := YoungDiagram.antitone_rowLen_add_ite_of_injective (hβ ▸ h)
  intro i j hij
  have := hanti hij
  simp only [rowLen_youngDiagram, ← val_strip_eq_ite] at this
  exact this

open Classical in
/-- **The dual Pieri rule for Schur polynomials in strip form**:
`e_r s_μ = Σ_{δ legal, |δ| = r} s_{μ + δ}`. -/
theorem esymm_mul_schurVec {F : Type*} [Field F] (r : ℕ) (mu : Nat.PartitionVector N) :
    esymm (Fin N) F r * schurVec F mu =
      ∑ δ : Strip N,
        if IsLegal mu δ ∧ stripWeight δ = r then schurVec F (addStrip mu δ) else 0 := by
  classical
  refine mul_right_cancel₀ (alternant_ne_zero_of_injective (R := F) (injective_staircase N)) ?_
  rw [mul_assoc, schurVec_mul_alternant, esymm_mul_alternant, Finset.sum_mul]
  have hterm (δ : Strip N) :
      (if IsLegal mu δ ∧ stripWeight δ = r then schurVec F (addStrip mu δ) else 0) *
          alternant (Fin N) F (fun j ↦ N - 1 - j) =
        if stripWeight δ = r then
          alternant (Fin N) F (fun j ↦ mu j + (N - 1 - j) + (δ j : ℕ)) else 0 := by
    split_ifs with h1 h2 h2
    · rw [schurVec_mul_alternant]
      congr 1
      funext j
      rw [addStrip_apply_of_legal h1.1]
      ring
    · exact absurd h1.2 h2
    · rw [zero_mul, alternant_eq_zero_of_not_injective fun h ↦ h1 ⟨isLegal_of_injective h, h2⟩]
    · rw [zero_mul]
  simp_rw [hterm]
  rw [← Finset.sum_filter, ← Finset.sum_equiv stripEquivFinset.symm (t := Finset.univ.filter
      fun δ : Strip N ↦ stripWeight δ = r)]
  · intro T
    simp [Finset.mem_powersetCard, stripWeight_eq_card]
  · intro T _
    congr 1
    funext j
    rw [val_strip_eq_ite, Equiv.apply_symm_apply]

/-- At `q = t` the Schur polynomials satisfy the generic-shaped vertical Pieri rule. -/
theorem satisfiesPolynomialPieri_schurVec {F : Type*} [Field F] {t : F}
    (ht : ∀ n : ℕ, n ≠ 0 → t ^ n ≠ 1) :
    SatisfiesPolynomialPieri (schurVec F : Nat.PartitionVector N → MvPolynomial (Fin N) F) t t := by
  intro r mu
  rw [esymm_mul_schurVec]
  refine Finset.sum_congr rfl fun δ _ ↦ ?_
  split_ifs with h
  · rw [pieriCoefficient_self_eq_one ht h.1, one_smul]
  · rfl

/-! ### Uniqueness from the Pieri rule -/

/-- The strip with one box in each nonzero row: the first column. -/
def firstColumn (lam : Nat.PartitionVector N) : Strip N := fun i ↦ if lam i = 0 then 0 else 1

/-- A partition vector with its first column removed. -/
def removeFirstColumn (lam : Nat.PartitionVector N) : Nat.PartitionVector N :=
  ⟨fun i ↦ lam i - 1, fun _ _ hij ↦ Nat.sub_le_sub_right (lam.antitone hij) 1⟩

/-- The value of the first-column strip. -/
theorem val_firstColumn (lam : Nat.PartitionVector N) (i : Fin N) :
    ((firstColumn lam i : Fin 2) : ℕ) = if lam i = 0 then 0 else 1 := by
  unfold firstColumn
  split_ifs <;> rfl

/-- Removing the first column and adding it back is coordinatewise the identity. -/
theorem removeFirstColumn_add_firstColumn (lam : Nat.PartitionVector N) (i : Fin N) :
    removeFirstColumn lam i + (firstColumn lam i : ℕ) = lam i := by
  rw [val_firstColumn]
  change lam i - 1 + _ = lam i
  split_ifs with h <;> lia

/-- The first column is a legal strip on the partition with its first column removed. -/
theorem isLegal_firstColumn (lam : Nat.PartitionVector N) :
    IsLegal (removeFirstColumn lam) (firstColumn lam) := by
  intro i j hij
  simp only [removeFirstColumn_add_firstColumn]
  exact lam.antitone hij

/-- Adding the first column back recovers the partition. -/
theorem addStrip_firstColumn (lam : Nat.PartitionVector N) :
    addStrip (removeFirstColumn lam) (firstColumn lam) = lam := by
  apply Nat.PartitionVector.ext
  intro i
  rw [addStrip_apply_of_legal (isLegal_firstColumn lam), removeFirstColumn_add_firstColumn]

/-- The first column has no contributing row pair, so its Pieri coefficient is one. -/
theorem pieriCoefficient_firstColumn {F : Type*} [Field F] (q t : F)
    (lam : Nat.PartitionVector N) :
    pieriCoefficient q t (removeFirstColumn lam) (firstColumn lam) = 1 := by
  have hempty : rowPairs (firstColumn lam) = ∅ := by
    ext ⟨i, j⟩
    simp only [mem_rowPairs, Finset.notMem_empty, iff_false, not_and]
    intro hij hi hj
    have hli : lam i = 0 := by
      by_contra h
      simp [firstColumn, h] at hi
    have hlj : lam j ≠ 0 := by
      intro h
      simp [firstColumn, h] at hj
    exact hlj (Nat.le_zero.mp (hli ▸ lam.antitone hij.le))
  simp [pieriCoefficient, pieriNum, pieriDen, hempty]

/-- Removing the first column of a nonzero partition makes it lexicographically smaller. -/
theorem lexKey_removeFirstColumn_lt {lam : Nat.PartitionVector N} (hlam : lam ≠ 0) :
    lexKey (removeFirstColumn lam) < lexKey lam := by
  apply Pi.toLex_strictMono
  refine Pi.lt_def.mpr ⟨fun i ↦ Nat.sub_le (lam i) 1, ?_⟩
  by_contra h
  push Not at h
  apply hlam
  apply Nat.PartitionVector.ext
  intro i
  have := h i
  change lam i ≤ lam i - 1 at this
  simp only [Nat.PartitionVector.zero_apply]
  lia

/-- Every other legal strip of the same size gives a lexicographically smaller partition than
adding back the first column. -/
theorem lexKey_addStrip_lt {lam : Nat.PartitionVector N} {δ : Strip N}
    (hδ : IsLegal (removeFirstColumn lam) δ)
    (hw : stripWeight δ = stripWeight (firstColumn lam)) (hne : δ ≠ firstColumn lam) :
    lexKey (addStrip (removeFirstColumn lam) δ) < lexKey lam := by
  classical
  have hs : (Finset.univ.filter fun i ↦ δ i ≠ firstColumn lam i).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at h
    exact hne (funext fun i ↦ by simpa using h (Finset.mem_univ i))
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ id hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hi0 hmin
  have hbefore (j : Fin N) (hj : j < i0) : δ j = firstColumn lam j := by
    by_contra h
    exact absurd (hmin j h) (not_le.mpr hj)
  rcases Fin.exists_fin_two.mp ⟨δ i0, rfl⟩ with hδ0 | hδ1
  · -- `δ` misses row `i0`, which the first column fills: lexicographically smaller.
    have hf : firstColumn lam i0 = 1 := by
      have := Fin.exists_fin_two.mp ⟨firstColumn lam i0, rfl⟩
      rcases this with h | h
      · exact absurd (hδ0.trans h.symm) hi0
      · exact h
    refine ⟨i0, fun j hj ↦ ?_, ?_⟩
    · change addStrip (removeFirstColumn lam) δ j = lam j
      rw [addStrip_apply_of_legal hδ, hbefore j hj, removeFirstColumn_add_firstColumn]
    · change addStrip (removeFirstColumn lam) δ i0 < lam i0
      rw [addStrip_apply_of_legal hδ, ← removeFirstColumn_add_firstColumn lam i0, hf, hδ0]
      simp
  · -- `δ` fills row `i0`, which the first column misses: then `δ` is too large.
    exfalso
    have hf : firstColumn lam i0 = 0 := by
      rcases Fin.exists_fin_two.mp ⟨firstColumn lam i0, rfl⟩ with h | h
      · exact h
      · exact absurd (hδ1.trans h.symm) hi0
    have hlam0 : lam i0 = 0 := by
      by_contra h
      simp [firstColumn, h] at hf
    have hzero (j : Fin N) (hj : ¬ j < i0) : ((firstColumn lam j : Fin 2) : ℕ) = 0 := by
      rw [val_firstColumn]
      simp [Nat.le_zero.mp (hlam0 ▸ lam.antitone (not_lt.mp hj))]
    have hsplit (f : Strip N) : stripWeight f =
        (∑ j ∈ Finset.univ.filter (· < i0), ((f j : Fin 2) : ℕ)) +
          ∑ j ∈ Finset.univ.filter (fun j ↦ ¬ j < i0), ((f j : Fin 2) : ℕ) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hfirst : (∑ j ∈ Finset.univ.filter (· < i0), ((δ j : Fin 2) : ℕ)) =
        ∑ j ∈ Finset.univ.filter (· < i0), ((firstColumn lam j : Fin 2) : ℕ) :=
      Finset.sum_congr rfl fun j hj ↦ by
        rw [hbefore j (Finset.mem_filter.mp hj).2]
    have hsecond0 : (∑ j ∈ Finset.univ.filter (fun j ↦ ¬ j < i0),
        ((firstColumn lam j : Fin 2) : ℕ)) = 0 :=
      Finset.sum_eq_zero fun j hj ↦ hzero j (Finset.mem_filter.mp hj).2
    have hsecond1 : 1 ≤ ∑ j ∈ Finset.univ.filter (fun j ↦ ¬ j < i0), ((δ j : Fin 2) : ℕ) := by
      have hmem : i0 ∈ Finset.univ.filter (fun j ↦ ¬ j < i0) := by simp
      have := Finset.single_le_sum (f := fun j ↦ ((δ j : Fin 2) : ℕ))
        (fun _ _ ↦ Nat.zero_le _) hmem
      simpa [hδ1] using this
    have h1 := hsplit δ
    have h2 := hsplit (firstColumn lam)
    lia

/-- **Uniqueness.**  Two families satisfying the same vertical Pieri rule and agreeing at the
empty partition are equal. -/
theorem eq_of_satisfiesPolynomialPieri {F : Type*} [Field F] {q t : F}
    {P Q : Nat.PartitionVector N → MvPolynomial (Fin N) F}
    (hP : SatisfiesPolynomialPieri P q t) (hQ : SatisfiesPolynomialPieri Q q t)
    (h0 : P 0 = Q 0) : P = Q := by
  classical
  funext lam
  induction lam using wellFounded_lexKey.induction with
  | _ lam ih =>
  by_cases hlam : lam = 0
  · rw [hlam]
    exact h0
  set mu := removeFirstColumn lam
  set δ0 := firstColumn lam
  have hsum := (hP (stripWeight δ0) mu).symm.trans
    ((congrArg _ (ih mu (lexKey_removeFirstColumn_lt hlam))).trans (hQ (stripWeight δ0) mu))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ δ0),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ δ0)] at hsum
  have hrest : ∀ δ ∈ Finset.univ.erase δ0,
      (if IsLegal mu δ ∧ stripWeight δ = stripWeight δ0 then
        pieriCoefficient q t mu δ • P (addStrip mu δ) else 0) =
      (if IsLegal mu δ ∧ stripWeight δ = stripWeight δ0 then
        pieriCoefficient q t mu δ • Q (addStrip mu δ) else 0) := by
    intro δ hδ
    split_ifs with h
    · rw [ih _ (lexKey_addStrip_lt h.1 h.2 (Finset.ne_of_mem_erase hδ))]
    · rfl
  rw [Finset.sum_congr rfl hrest, add_left_inj] at hsum
  split_ifs at hsum with hc
  · rwa [pieriCoefficient_firstColumn, one_smul, one_smul, addStrip_firstColumn] at hsum
  · exact absurd ⟨isLegal_firstColumn lam, rfl⟩ hc

/-! ### The specialized basis at `q = t` -/

/-- The polynomial family underlying a basis satisfying `SatisfiesPieri` satisfies the
polynomial form of the rule. -/
theorem SatisfiesPieri.satisfiesPolynomialPieri {F : Type*} [Field F]
    {b : Module.Basis (Nat.PartitionVector N) F (symmetricSubalgebra (Fin N) F)} {q t : F}
    (h : SatisfiesPieri b q t) :
    SatisfiesPolynomialPieri (fun lam ↦ (b lam : MvPolynomial (Fin N) F)) q t := by
  intro r lam
  have h' := congrArg Subtype.val (h r lam)
  simp only [MulMemClass.coe_mul, AddSubmonoidClass.coe_finsetSum] at h'
  refine h'.trans (Finset.sum_congr rfl fun δ _ ↦ ?_)
  split_ifs
  · rfl
  · rfl

/-- `ℚ(q, t)`, the field of the generic Macdonald polynomials. -/
local notation "𝕂" => FractionRing (MvPolynomial (Fin 2) ℚ)

variable {P : Nat.PartitionVector N → MvPolynomial (Fin N) 𝕂}

/-- **The `q = t` specialization is the Schur basis.**  For a lex-unitriangular family over
`ℚ(q, t)` satisfying the generic Pieri rule, the specialized basis at `q = t` consists of the
Schur polynomials. -/
theorem coe_specializedBasis_diagonal (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hPieri : SatisfiesPolynomialPieri P (algebraMap (MvPolynomial (Fin 2) ℚ) 𝕂 (X 0))
      (algebraMap (MvPolynomial (Fin 2) ℚ) 𝕂 (X 1)))
    (lam : Nat.PartitionVector N) :
    (specializedBasis diagonalSpecialization (X 0) (X 1)
        pieriDen_diagonalSpecialization_ne_zero hP hPieri lam :
          MvPolynomial (Fin N) (FractionRing ℚ[X])) =
      schurVec (FractionRing ℚ[X]) lam := by
  have hB := (satisfiesPieri_specializedBasis diagonalSpecialization (X 0) (X 1)
    pieriDen_diagonalSpecialization_ne_zero hP hPieri).satisfiesPolynomialPieri
  rw [diagonalSpecialization_X_zero, diagonalSpecialization_X_one] at hB
  have hS := satisfiesPolynomialPieri_schurVec (N := N)
    (fun _ hn ↦ ratFuncVar_pow_ne_one ℚ hn)
  have h0 : (fun lam ↦ (specializedBasis diagonalSpecialization (X 0) (X 1)
      pieriDen_diagonalSpecialization_ne_zero hP hPieri lam :
        MvPolynomial (Fin N) (FractionRing ℚ[X]))) 0 = schurVec (FractionRing ℚ[X]) 0 := by
    simp [specializedBasis_zero]
  exact congrFun (eq_of_satisfiesPolynomialPieri hB hS h0) lam

/-- A ring homomorphism commutes with evaluation after mapping the coefficients. -/
theorem map_eval_eq_eval_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (y : Fin N → R) (p : MvPolynomial (Fin N) R) : f (eval y p) = eval (f ∘ y) (map f p) := by
  rw [eval_map]
  change f (eval₂ (RingHom.id R) y p) = _
  rw [eval₂_comp_left, RingHom.comp_id]

/-- **Pieri ledger Lemma 8: `u_0(P_λ) ≠ 0`.**  For a lex-unitriangular family over `ℚ(q, t)`
satisfying the generic Pieri rule, the evaluation at `x_i = t ^ (N - 1 - i)` is nonzero.  At
`q = t` this evaluation specializes to the principal Schur evaluation, which is nonzero. -/
theorem eval_staircase_ne_zero (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hPieri : SatisfiesPolynomialPieri P (algebraMap (MvPolynomial (Fin 2) ℚ) 𝕂 (X 0))
      (algebraMap (MvPolynomial (Fin 2) ℚ) 𝕂 (X 1)))
    (lam : Nat.PartitionVector N) :
    eval (fun i : Fin N ↦ algebraMap (MvPolynomial (Fin 2) ℚ) 𝕂 (X 1) ^ (N - 1 - (i : ℕ)))
      (P lam) ≠ 0 := by
  set φ := diagonalSpecialization
  set O := Localization.AtPrime (RingHom.ker φ)
  have hinj := algebraMap_localization_fractionRing_injective φ
  have hmul := esymm_mul_mem_span φ (X 0) (X 1) pieriDen_diagonalSpecialization_ne_zero hPieri
  set Q := regularLift hinj hP hmul lam
  set y : Fin N → O := fun i ↦ algebraMap (MvPolynomial (Fin 2) ℚ) O (X 1) ^ (N - 1 - (i : ℕ))
  have hK : eval (fun i : Fin N ↦ algebraMap (MvPolynomial (Fin 2) ℚ) 𝕂 (X 1) ^ (N - 1 - (i : ℕ)))
      (P lam) = algebraMap O 𝕂 (eval y Q) := by
    have hy : ⇑(algebraMap O 𝕂) ∘ y =
        fun i : Fin N ↦ algebraMap (MvPolynomial (Fin 2) ℚ) 𝕂 (X 1) ^ (N - 1 - (i : ℕ)) := by
      funext i
      simp [y, ← IsScalarTower.algebraMap_apply]
    rw [map_eval_eq_eval_map, map_regularLift, hy]
  have hF : specializationHom φ (eval y Q) =
      eval (fun i : Fin N ↦ ratFuncVar ℚ ^ (N - 1 - (i : ℕ))) (schurVec _ lam) := by
    have hy : ⇑(specializationHom φ) ∘ y = fun i : Fin N ↦ ratFuncVar ℚ ^ (N - 1 - (i : ℕ)) := by
      funext i
      simp only [Function.comp_apply, map_pow, y]
      rw [specializationHom_algebraMap, diagonalSpecialization_X_one]
    rw [map_eval_eq_eval_map, ← coe_specializedBasis_diagonal hP hPieri lam,
      coe_specializedBasis, hy]
  rw [hK]
  intro h0
  have h1 : eval y Q = 0 := hinj (by rw [h0, map_zero])
  apply eval_schurVec_ne_zero (injective_pow_ratFuncVar ℚ) lam
  rw [← hF, h1, map_zero]

/-- **Pieri ledger Lemma 8 for the Macdonald polynomials, conditional on the generic Pieri rule**:
`u_0(P_λ) = P_λ(t ^ (N - 1), …, t, 1) ≠ 0` in `ℚ(q, t)`.  The hypothesis `hPieri` is the vertical
Pieri rule for `macdonaldP` (Pieri ledger Lemma 15), not yet proved. -/
theorem eval_grid_zero_macdonaldP_ne_zero
    (hPieri : SatisfiesPolynomialPieri (macdonaldP (N := N)) macdonaldParamQ macdonaldParamT)
    (lam : Nat.PartitionVector N) :
    eval (grid macdonaldParamQ macdonaldParamT 0) (macdonaldP lam) ≠ 0 := by
  have hgrid : grid macdonaldParamQ macdonaldParamT (0 : Nat.PartitionVector N) =
      fun i : Fin N ↦ algebraMap (MvPolynomial (Fin 2) ℚ) 𝕂 (X 1) ^ (N - 1 - (i : ℕ)) := by
    funext i
    simp [grid, staircase]
  rw [hgrid]
  exact eval_staircase_ne_zero isLexUnitriangular_macdonaldP hPieri lam

end PartitionDivision
