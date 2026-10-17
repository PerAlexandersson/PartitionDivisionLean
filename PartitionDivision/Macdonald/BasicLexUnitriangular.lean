/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Macdonald.Basic
public import PartitionDivision.Macdonald.LexUnitriangular

/-!
# The Macdonald polynomials are lex-unitriangular

`MvPolynomial.macdonaldP λ` is characterized in `PartitionDivision.Macdonald.Basic` by
`P_λ - m_λ ∈ span {m_μ : |μ| = |λ|, μ <_lex λ}`, with the lexicographic order on finitely
supported exponent vectors.  This file translates that into the coefficient form
`IsLexUnitriangular` of `PartitionDivision.Macdonald.LexUnitriangular`, which uses the
lexicographic order on functions (`lexKey`).  The two orders agree (`lexKey_lt_iff`).
-/

@[expose] public section

noncomputable section

namespace PartitionDivision.Macdonald

open MvPolynomial

variable {N : ℕ}

/-- The lexicographic order on partition vectors used by `lexKey` agrees with the lexicographic
order on their finitely supported exponent vectors. -/
theorem lexKey_lt_iff (mu lam : Nat.PartitionVector N) :
    lexKey mu < lexKey lam ↔
      toLex (partitionVectorFinsupp mu) < toLex (partitionVectorFinsupp lam) := by
  rw [Finsupp.Lex.lt_iff]
  simp only [ofLex_toLex, partitionVectorFinsupp_apply]
  rfl

/-- Every element of the span of the monomial symmetric polynomials `m_μ` with `μ <_lex λ` has
zero coefficient at every partition vector `ν` with `λ ≤_lex ν`. -/
theorem coeff_eq_zero_of_mem_span_lexLower {K : Type*} [Field K] {n : ℕ}
    {lam : Nat.PartitionVector N} {x : MvPolynomial (Fin N) K}
    (hx : x ∈ Submodule.span K (msymmVec K '' lexLowerPartitionVectors n lam))
    {nu : Nat.PartitionVector N} (hnu : lexKey lam ≤ lexKey nu) :
    x.coeff (partitionVectorFinsupp nu) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨mu, hmu, rfl⟩ := hx
      have hlt : lexKey mu < lexKey lam := (lexKey_lt_iff mu lam).mpr hmu.2
      have hne : nu ≠ mu := by
        rintro rfl
        exact hlt.not_ge hnu
      simp [coeff_msymmVec_partitionVectorFinsupp, hne]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

/-- **The Macdonald polynomial `P_λ` is lex-unitriangular with leading index `λ`.** -/
theorem isLexUnitriangular_macdonaldP (lam : Nat.PartitionVector N) :
    IsLexUnitriangular (macdonaldP lam) lam := by
  have hsplit : macdonaldP lam =
      msymmVec (FractionRing (MvPolynomial (Fin 2) ℚ)) lam +
        (macdonaldP lam - msymmVec (FractionRing (MvPolynomial (Fin 2) ℚ)) lam) := by
    rw [add_sub_cancel]
  have hspan := macdonaldP_sub_msymmVec_mem_span lam
  refine ⟨macdonaldP_isSymmetric lam, ?_, fun mu hmu ↦ ?_⟩
  · rw [hsplit, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      coeff_eq_zero_of_mem_span_lexLower hspan le_rfl, coeff_msymmVec_partitionVectorFinsupp]
    simp
  · have hne : mu ≠ lam := by
      rintro rfl
      exact hmu.false
    rw [hsplit, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      coeff_eq_zero_of_mem_span_lexLower hspan hmu.le, coeff_msymmVec_partitionVectorFinsupp]
    simp [hne]

end PartitionDivision.Macdonald
