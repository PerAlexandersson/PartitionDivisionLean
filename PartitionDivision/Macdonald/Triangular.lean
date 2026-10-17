/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import PartitionDivision.Macdonald.Operator
public import PartitionDivision.Mathlib.RingTheory.MvPolynomial.Symmetric.MonomialBasis

/-!
# Lexicographic triangularity of the Macdonald operators

We use the lexicographic monomial order `MonomialOrder.lex` on `Fin N →₀ ℕ`, in which the
variable `X 0` is the largest.  In this order:

* the Vandermonde polynomial is monic with leading exponent the staircase
  `δ = (N - 1, N - 2, …, 0)` (`lex_degree_vandermonde`, `lex_monic_vandermonde`);
* the monomial symmetric polynomial `msymmVec K λ` is monic with leading exponent `λ`
  (`lex_degree_msymmVec`, `lex_monic_msymmVec`);
* simultaneous variable scaling multiplies each coefficient by a scalar (`coeff_scaleVars`).

Comparing the coefficients of `vandermonde * macdonaldOp q t r m_λ` at `δ + λ` gives the
triangularity theorem `macdonaldOp_msymmVec_sub_mem_span`: the image of `m_λ` is
`ε_r(λ) m_λ` plus a combination of `m_μ` with `|μ| = |λ|` and `μ` lexicographically below `λ`.
-/

@[expose] public section

noncomputable section

open Finset
open scoped MonomialOrder

namespace MvPolynomial

variable {N : ℕ} {K : Type*}

variable {N : ℕ} {K : Type*}

/-- The staircase exponent vector `δ`, with `δ i = N - 1 - i`. -/
def vandermondeExponent (N : ℕ) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ (Fin.rev i).val

@[simp]
theorem vandermondeExponent_apply (i : Fin N) :
    vandermondeExponent N i = (Fin.rev i).val := by
  simp [vandermondeExponent]

/-- For `i < j`, the lexicographic leading exponent of `X i - X j` is that of `X i`. -/
theorem lex_degree_X_sub_X [CommRing K] [Nontrivial K] {i j : Fin N} (hij : i < j) :
    MonomialOrder.lex.degree (X i - X j : MvPolynomial (Fin N) K) = Finsupp.single i 1 := by
  have hlt : MonomialOrder.lex.degree (X j : MvPolynomial (Fin N) K) ≺[MonomialOrder.lex]
      MonomialOrder.lex.degree (X i : MvPolynomial (Fin N) K) := by
    rw [MonomialOrder.degree_X, MonomialOrder.degree_X, MonomialOrder.lex_lt_iff]
    exact Finsupp.Lex.single_lt_iff.mpr hij
  rw [MonomialOrder.degree_sub_of_lt hlt, MonomialOrder.degree_X]

/-- For `i < j`, the polynomial `X i - X j` is lexicographically monic. -/
theorem lex_monic_X_sub_X [CommRing K] {i j : Fin N} (hij : i < j) :
    MonomialOrder.lex.Monic (X i - X j : MvPolynomial (Fin N) K) := by
  nontriviality K
  have hlt : MonomialOrder.lex.degree (X j : MvPolynomial (Fin N) K) ≺[MonomialOrder.lex]
      MonomialOrder.lex.degree (X i : MvPolynomial (Fin N) K) := by
    rw [MonomialOrder.degree_X, MonomialOrder.degree_X, MonomialOrder.lex_lt_iff]
    exact Finsupp.Lex.single_lt_iff.mpr hij
  rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff_sub_of_lt hlt,
    MonomialOrder.leadingCoeff_X]

/-- The Vandermonde polynomial is lexicographically monic. -/
theorem lex_monic_vandermonde [CommRing K] :
    MonomialOrder.lex.Monic (vandermonde N K) := by
  rw [vandermonde]
  exact MonomialOrder.Monic.prod fun i _ ↦ MonomialOrder.Monic.prod fun j hj ↦
    lex_monic_X_sub_X (Finset.mem_Ioi.mp hj)

/-- The lexicographic leading exponent of the Vandermonde polynomial is the staircase `δ`. -/
theorem lex_degree_vandermonde [CommRing K] [Nontrivial K] :
    MonomialOrder.lex.degree (vandermonde N K) = vandermondeExponent N := by
  have hreg (i : Fin N) (j : Fin N) (hj : j ∈ Finset.Ioi i) :
      IsRegular (MonomialOrder.lex.leadingCoeff (X i - X j : MvPolynomial (Fin N) K)) := by
    rw [(lex_monic_X_sub_X (Finset.mem_Ioi.mp hj)).leadingCoeff_eq_one]
    exact isRegular_one
  have hinner (i : Fin N) :
      MonomialOrder.lex.degree (∏ j ∈ Finset.Ioi i, (X i - X j : MvPolynomial (Fin N) K)) =
        Finsupp.single i (#(Finset.Ioi i)) := by
    rw [MonomialOrder.degree_prod_of_regular (hreg i)]
    rw [Finset.sum_congr rfl fun j hj ↦ lex_degree_X_sub_X (K := K) (Finset.mem_Ioi.mp hj)]
    simp
  rw [vandermonde, MonomialOrder.degree_prod_of_regular]
  · simp_rw [hinner]
    ext k
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, vandermondeExponent_apply, Fin.card_Ioi, Fin.val_rev]
    lia
  · intro i _
    rw [(MonomialOrder.Monic.prod fun j hj ↦
      lex_monic_X_sub_X (K := K) (Finset.mem_Ioi.mp hj)).leadingCoeff_eq_one]
    exact isRegular_one

/-- Simultaneous scaling acts on a monomial by a scalar. -/
theorem scaleVars_monomial [CommSemiring K] (c : K) (I : Finset (Fin N))
    (d : Fin N →₀ ℕ) (a : K) :
    scaleVars c I (monomial d a) = monomial d (a * ∏ i ∈ I, c ^ d i) := by
  change aeval (fun j ↦ if j ∈ I then c • X j else X j) (monomial d a) = _
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  have hfac (j : Fin N) :
      (if j ∈ I then c • X j else X j : MvPolynomial (Fin N) K) ^ d j =
        C (if j ∈ I then c ^ d j else 1) * X j ^ d j := by
    split_ifs <;> simp [smul_eq_C_mul, mul_pow]
  simp_rw [hfac, Finset.prod_mul_distrib, ← map_prod, Finset.prod_ite_mem, Finset.univ_inter]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), algebraMap_eq, C_mul]
  ring

/-- The coefficients of a simultaneously scaled polynomial. -/
theorem coeff_scaleVars [CommSemiring K] (c : K) (I : Finset (Fin N))
    (f : MvPolynomial (Fin N) K) (d : Fin N →₀ ℕ) :
    (scaleVars c I f).coeff d = (∏ i ∈ I, c ^ d i) * f.coeff d := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial e a =>
      rw [scaleVars_monomial, coeff_monomial, coeff_monomial]
      split_ifs with h
      · subst h
        ring
      · simp
  | add f g hf hg => simp [hf, hg, mul_add]

/-- Simultaneous scaling does not raise the lexicographic degree. -/
theorem lex_degree_scaleVars_le [CommSemiring K] (c : K) (I : Finset (Fin N))
    (f : MvPolynomial (Fin N) K) :
    MonomialOrder.lex.degree (scaleVars c I f) ≼[MonomialOrder.lex]
      MonomialOrder.lex.degree f := by
  rw [MonomialOrder.degree_le_iff]
  intro b hb
  apply MonomialOrder.le_degree
  rw [mem_support_iff, coeff_scaleVars] at hb
  exact mem_support_iff.mpr (right_ne_zero_of_mul hb)

/-- If `f` has lexicographic degree at most `mu`, every summand of the `r`-th numerator, and
hence the numerator itself, has degree at most `δ + mu`. -/
theorem lex_degree_macdonaldOpNumerator_le [CommRing K] [Nontrivial K] (q t : K) (r : ℕ)
    {f : MvPolynomial (Fin N) K} {mu : Fin N →₀ ℕ}
    (hf : MonomialOrder.lex.degree f ≼[MonomialOrder.lex] mu) :
    MonomialOrder.lex.degree (macdonaldOpNumerator q t r f) ≼[MonomialOrder.lex]
      vandermondeExponent N + mu := by
  rw [macdonaldOpNumerator]
  refine MonomialOrder.degree_sum_le.trans (Finset.sup_le fun I _ ↦ ?_)
  refine MonomialOrder.degree_mul_le.trans ?_
  rw [map_add, map_add]
  refine add_le_add ((lex_degree_scaleVars_le t I _).trans (le_of_eq ?_))
    ((lex_degree_scaleVars_le q I f).trans hf)
  rw [lex_degree_vandermonde]

/-- If `f` has lexicographic degree at most `mu`, the coefficient of the `r`-th numerator at
`δ + mu` is the `r`-th Macdonald eigenvalue at `mu` times the coefficient of `f` at `mu`. -/
theorem coeff_macdonaldOpNumerator_of_degree_le [CommRing K] [Nontrivial K] (q t : K) (r : ℕ)
    {f : MvPolynomial (Fin N) K} {mu : Fin N →₀ ℕ}
    (hf : MonomialOrder.lex.degree f ≼[MonomialOrder.lex] mu) :
    (macdonaldOpNumerator q t r f).coeff (vandermondeExponent N + mu) =
      macdonaldEigenvalueR q t r mu * f.coeff mu := by
  have hv : (vandermonde N K).coeff (vandermondeExponent N) = 1 := by
    rw [← lex_degree_vandermonde (K := K)]
    exact lex_monic_vandermonde.coeff_degree
  rw [macdonaldOpNumerator, coeff_sum, macdonaldEigenvalueR, Finset.sum_mul]
  refine Finset.sum_congr rfl fun I _ ↦ ?_
  rw [MonomialOrder.coeff_mul_of_add_of_degree_le
    ((lex_degree_scaleVars_le t I _).trans (le_of_eq (by rw [lex_degree_vandermonde])))
    ((lex_degree_scaleVars_le q I f).trans hf),
    coeff_scaleVars, coeff_scaleVars, hv, Finset.prod_mul_distrib]
  simp only [vandermondeExponent_apply]
  ring

/-- If all exponents of `vandermonde * g` are lexicographically below `δ + lam`, then all
exponents of `g` are below `lam`. -/
theorem lex_lt_of_mem_support_of_vandermonde_mul [CommRing K] [IsDomain K]
    {g : MvPolynomial (Fin N) K} {lam : Fin N →₀ ℕ}
    (h : ∀ b ∈ (vandermonde N K * g).support,
      b ≺[MonomialOrder.lex] vandermondeExponent N + lam)
    {b : Fin N →₀ ℕ} (hb : b ∈ g.support) : b ≺[MonomialOrder.lex] lam := by
  have hg : g ≠ 0 := by
    rintro rfl
    simp at hb
  have hprod : vandermonde N K * g ≠ 0 := mul_ne_zero (vandermonde_ne_zero N K) hg
  have hdeg := h _ (MonomialOrder.lex.degree_mem_support hprod)
  rw [MonomialOrder.degree_mul (vandermonde_ne_zero N K) hg, lex_degree_vandermonde,
    map_add, map_add] at hdeg
  exact (MonomialOrder.le_degree hb).trans_lt (lt_of_add_lt_add_left hdeg)

/-- The monomial symmetric polynomial `msymmVec K λ` has lexicographic leading exponent `λ`. -/
theorem lex_degree_msymmVec [CommSemiring K] [Nontrivial K] (lambda : Nat.PartitionVector N) :
    MonomialOrder.lex.degree (msymmVec K lambda) = partitionVectorFinsupp lambda := by
  apply MonomialOrder.lex.toSyn.injective
  apply le_antisymm
  · rw [MonomialOrder.degree_le_iff]
    intro b hb
    rw [mem_support_iff, coeff_msymmVec] at hb
    split_ifs at hb with h
    · exact toLex_le_partitionVectorFinsupp_of_mem h
    · exact absurd rfl hb
  · apply MonomialOrder.le_degree
    rw [mem_support_iff, coeff_msymmVec_partitionVectorFinsupp]
    simp

/-- The monomial symmetric polynomial `msymmVec K λ` is lexicographically monic. -/
theorem lex_monic_msymmVec [CommSemiring K] (lambda : Nat.PartitionVector N) :
    MonomialOrder.lex.Monic (msymmVec K lambda) := by
  nontriviality K
  rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff, lex_degree_msymmVec,
    coeff_msymmVec_partitionVectorFinsupp]
  simp

/-- The partition-vector monomial symmetric polynomial as an element of the symmetric
subalgebra. -/
def msymmVecSym (K : Type*) [CommSemiring K] (lambda : Nat.PartitionVector N) :
    symmetricSubalgebra (Fin N) K :=
  ⟨msymmVec K lambda, msymmVec_isSymmetric K lambda⟩

@[simp]
theorem coe_msymmVecSym (K : Type*) [CommSemiring K] (lambda : Nat.PartitionVector N) :
    (msymmVecSym K lambda : MvPolynomial (Fin N) K) = msymmVec K lambda :=
  rfl

/-- **Triangularity of the Macdonald operators.**  For a partition vector `λ`,
`D^r m_λ - ε_r(λ) m_λ` is a combination of the `m_μ` with `|μ| = |λ|` and `μ`
lexicographically smaller than `λ`.  Here `ε_r(λ) = Σ_{|I| = r} ∏_{i ∈ I} q ^ λ i t ^ (N-1-i)`
is `macdonaldEigenvalueR q t r λ`. -/
theorem macdonaldOp_msymmVec_sub_mem_span [Field K] [CharZero K] (q t : K) (r : ℕ)
    (lambda : Nat.PartitionVector N) :
    (macdonaldOp q t r (msymmVecSym K lambda) : MvPolynomial (Fin N) K) -
        macdonaldEigenvalueR q t r lambda • msymmVec K lambda ∈
      Submodule.span K (msymmVec K '' {mu | partitionVectorDegree mu =
        partitionVectorDegree lambda ∧
          toLex (partitionVectorFinsupp mu) < toLex (partitionVectorFinsupp lambda)}) := by
  set lam := partitionVectorFinsupp lambda with hlam
  set eps := macdonaldEigenvalueR q t r lambda with heps
  set g := (macdonaldOp q t r (msymmVecSym K lambda) : MvPolynomial (Fin N) K) -
    eps • msymmVec K lambda with hg
  have hsym : g.IsSymmetric :=
    (macdonaldOp q t r (msymmVecSym K lambda)).2.sub
      ((msymmVec_isSymmetric K lambda).smul eps)
  have hhom : g.IsHomogeneous (partitionVectorDegree lambda) :=
    (homogeneousSubmodule (Fin N) K _).sub_mem
      (IsHomogeneous.macdonaldOp q t r (isHomogeneous_msymmVec K lambda))
      ((homogeneousSubmodule (Fin N) K _).smul_mem eps (isHomogeneous_msymmVec K lambda))
  have hdeg : MonomialOrder.lex.degree (msymmVec K lambda) ≼[MonomialOrder.lex] lam :=
    le_of_eq (by rw [lex_degree_msymmVec])
  have hprod : vandermonde N K * g = macdonaldOpNumerator q t r (msymmVec K lambda) -
      eps • (vandermonde N K * msymmVec K lambda) := by
    rw [hg, mul_sub, vandermonde_mul_macdonaldOp, mul_smul_comm]
    rfl
  have hvm_deg : MonomialOrder.lex.degree (vandermonde N K * msymmVec K lambda)
      ≼[MonomialOrder.lex] vandermondeExponent N + lam := by
    refine MonomialOrder.degree_mul_le.trans ?_
    rw [lex_degree_vandermonde, lex_degree_msymmVec]
  have hvm_coeff : (vandermonde N K * msymmVec K lambda).coeff
      (vandermondeExponent N + lam) = 1 := by
    rw [MonomialOrder.coeff_mul_of_add_of_degree_le (le_of_eq (by rw [lex_degree_vandermonde]))
      hdeg]
    rw [← lex_degree_vandermonde (K := K), lex_monic_vandermonde.coeff_degree, hlam,
      coeff_msymmVec_partitionVectorFinsupp]
    simp
  have hlow : ∀ b ∈ (vandermonde N K * g).support,
      b ≺[MonomialOrder.lex] vandermondeExponent N + lam := by
    intro b hb
    rw [hprod] at hb
    have hle : b ≼[MonomialOrder.lex] vandermondeExponent N + lam := by
      refine (MonomialOrder.le_degree hb).trans (MonomialOrder.degree_sub_le.trans ?_)
      refine sup_le (lex_degree_macdonaldOpNumerator_le q t r hdeg) ?_
      exact MonomialOrder.degree_smul_le.trans hvm_deg
    refine lt_of_le_of_ne hle fun heq ↦ ?_
    have hbeq : b = vandermondeExponent N + lam := MonomialOrder.lex.toSyn.injective heq
    rw [mem_support_iff, hbeq, coeff_sub, coeff_smul,
      coeff_macdonaldOpNumerator_of_degree_le q t r hdeg, hvm_coeff, hlam,
      coeff_msymmVec_partitionVectorFinsupp] at hb
    simp [heps] at hb
  refine hsym.mem_span_msymmVec fun mu hmu ↦ ⟨hhom.partitionVectorDegree_eq hmu, ?_⟩
  exact lex_lt_of_mem_support_of_vandermonde_mul hlow hmu

end MvPolynomial
