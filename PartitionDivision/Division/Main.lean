/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import PartitionDivision.Division.MacdonaldPieri
public import PartitionDivision.Division.RootOfUnity
public import PartitionDivision.Macdonald.BasicLexUnitriangular
public import PartitionDivision.Macdonald.DiagonalRegularity
public import PartitionDivision.Macdonald.JointEigen
public import PartitionDivision.Macdonald.Rectangle

/-!
# The partition-division theorem, assembled

This file chains the Macdonald layer to the root-of-unity argument:

1. `satisfiesPolynomialPieri_macdonaldP`: the generic Pieri rule for `macdonaldP`, given
   ledger Lemmas 7 and 8;
2. `Macdonald.isLexUnitriangular_macdonaldP`;
3. `specializedBasis` at `rootSpecialization ζ` (`q ↦ ζ`, `t ↦ ζ v`), which gives
   `macdonaldRootBasis ζ` over `RationalFunction L = FractionRing L[X]`, with the Pieri rule at
   `(constantRationalFunction ζ, scaledVariableRationalFunction ζ)` and value `1` at `0`;
4. `exists_nat_esymm_expansion_of_pieri_at_root_of_unity`;
5. `L = CyclotomicField k ℚ` with `ζ = IsCyclotomicExtension.zeta k ℚ L`.

The Macdonald inputs were first stated as separate, named hypotheses:

* `Macdonald.MacdonaldJointEigen` (ledger Lemma 7), proved as `Macdonald.macdonaldJointEigen`;
* `MacdonaldBaseEvalNeZero` (ledger Lemma 8), proved as `macdonaldBaseEvalNeZero`;
* `MacdonaldRootRectangles` (the rectangle values of the specialized basis), proved as
  `macdonaldRootRectangles` from `Macdonald.satisfiesRectangles_of_macdonaldD_eigenvectors`.

The final theorem `exponentDiv_esymmPart_ePositive` has no hypotheses beyond
`0 < k`, `n ≤ N` and `μ ⊢ k n`.
-/

@[expose] public section

noncomputable section

open MvPolynomial Polynomial

namespace PartitionDivision

variable {N : ℕ}

/-- **Hypothesis (ledger Lemma 8).**  The base evaluation `u_0(P_λ) = P_λ(t ^ (N - 1), …, t, 1)`
of every Macdonald polynomial is nonzero in `ℚ(q, t)`. -/
def MacdonaldBaseEvalNeZero (N : ℕ) : Prop :=
  ∀ lam : Nat.PartitionVector N, eval (Macdonald.pieriGrid 0) (macdonaldP lam) ≠ 0

/-- The Macdonald basis specialized at `q = ζ`, `t = ζ v`: a basis of the symmetric polynomials
over `L(v) = RationalFunction L`.  It depends on the Lemma 7 and Lemma 8 hypotheses only through
the generic Pieri rule used to prove regularity at `(ζ, ζ v)`. -/
def macdonaldRootBasis {L : Type*} [Field L] [CharZero L] (ζ : L)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N) :
    Module.Basis (Nat.PartitionVector N) (RationalFunction L)
      (symmetricSubalgebra (Fin N) (RationalFunction L)) :=
  specializedBasis (Macdonald.rootSpecialization ζ) (MvPolynomial.X 0) (MvPolynomial.X 1)
    (Macdonald.pieriDen_rootSpecialization_ne_zero ζ) Macdonald.isLexUnitriangular_macdonaldP
    (satisfiesPolynomialPieri_macdonaldP heig hne)

/-- The specialized Macdonald basis satisfies the vertical Pieri rule at `(ζ, ζ v)` in the
encoding of `Division.RootOfUnity`. -/
theorem satisfiesPieri_macdonaldRootBasis {L : Type*} [Field L] [CharZero L] (ζ : L)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N) :
    SatisfiesPieri (macdonaldRootBasis ζ heig hne) (constantRationalFunction ζ)
      (scaledVariableRationalFunction ζ) := by
  have h := (satisfiesPieri_rootSpecialization ζ
    Macdonald.isLexUnitriangular_macdonaldP (satisfiesPolynomialPieri_macdonaldP heig hne)).1
  have hscaled : scaledVariableRationalFunction ζ =
      algebraMap L[X] (FractionRing L[X]) (Polynomial.C ζ) *
        algebraMap L[X] (FractionRing L[X]) Polynomial.X := by
    rw [scaledVariableRationalFunction, map_mul]
  rw [hscaled]
  exact h

/-- The specialized Macdonald basis vector at the empty partition is `1`. -/
theorem macdonaldRootBasis_zero {L : Type*} [Field L] [CharZero L] (ζ : L)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N) :
    macdonaldRootBasis ζ heig hne 0 = 1 :=
  (satisfiesPieri_rootSpecialization ζ
    Macdonald.isLexUnitriangular_macdonaldP (satisfiesPolynomialPieri_macdonaldP heig hne)).2

/-- **Hypothesis (rectangle values).**  For every field `L` of characteristic zero and every
primitive `k`-th root of unity `ζ ∈ L`, the specialized Macdonald basis at `(ζ, ζ v)` sends the
rectangles `k • (1 ^ h)`, `1 ≤ h ≤ N`, to `e_h(x_1 ^ k, …, x_N ^ k)`. -/
def MacdonaldRootRectangles (heig : Macdonald.MacdonaldJointEigen (N := N))
    (hne : MacdonaldBaseEvalNeZero N) (k : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [CharZero L] (ζ : L), IsPrimitiveRoot ζ k →
    SatisfiesRectangles (macdonaldRootBasis ζ heig hne) k

/-- The partition-division theorem at a single primitive root of unity `ζ ∈ L`, assuming
ledger Lemmas 7 and 8 and the rectangle values of the specialized basis at this `ζ`. -/
theorem exponentDiv_esymmPart_ePositive_of_root {k n : ℕ} (hk : 0 < k)
    (hn : n ≤ N) (mu : (k * n).Partition) {L : Type*} [Field L] [CharZero L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ k)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N)
    (hrect : SatisfiesRectangles (macdonaldRootBasis ζ heig hne) k) :
    ∃ c : n.Partition → ℕ,
      exponentDiv k (esymmPart (Fin N) ℤ mu) = ∑ nu, c nu • esymmPart (Fin N) ℤ nu :=
  exists_nat_esymm_expansion_of_pieri_at_root_of_unity hk hn mu hζ
    (macdonaldRootBasis ζ heig hne) (satisfiesPieri_macdonaldRootBasis ζ heig hne)
    (macdonaldRootBasis_zero ζ heig hne) hrect

/-- Ledger Lemma 8 in the form used here: `u_0(P_λ) ≠ 0`, proved without the Pieri rule
(`PartitionDivision.Macdonald.eval_grid_zero_macdonaldP_ne_zero`). -/
theorem macdonaldBaseEvalNeZero (N : ℕ) : MacdonaldBaseEvalNeZero N := fun lam ↦ by
  have h := Macdonald.eval_grid_zero_macdonaldP_ne_zero lam
  rwa [Macdonald.grid_eq_pieriGrid] at h

/-- **The partition-division theorem** in `N` variables.

For `0 < k`, `n ≤ N` and a partition `μ ⊢ k n`, the exponent division `R_k = exponentDiv k`
sends `e_μ` to a natural-number combination of the `e_ν`, `ν ⊢ n`.

**Assumed** (each an explicit hypothesis, to be dropped once proved):
* `heig : Macdonald.MacdonaldJointEigen`: ledger Lemma 7, the joint eigenvalue equation
  `D^r P_λ = ε_r(λ) P_λ` for all `r`, in numerator form;
* `hne : MacdonaldBaseEvalNeZero N`: ledger Lemma 8, `u_0(P_λ) ≠ 0`;
* `hrect : MacdonaldRootRectangles heig hne k`: the rectangle values
  `P_{k • 1^h}(x; ζ, ζ v) = e_h(x ^ k)` of the specialized basis at every primitive `k`-th root
  of unity in a field of characteristic zero.  Only the instance
  `L = CyclotomicField k ℚ`, `ζ = IsCyclotomicExtension.zeta k ℚ L` is used.

Everything else is proved: the generic Pieri rule from Lemmas 7 and 8, lex-unitriangularity,
regularity and specialization at `(ζ, ζ v)`, and the root-of-unity transition argument.

**Remark (relation to symmetric functions).**  `exponentDiv k` is the operator `R_k` restricted
to `N` variables: it keeps the monomials whose exponents are all divisible by `k` and divides
those exponents by `k`.  Restriction to `N` variables commutes with `R_k`, and for `N ≥ n` the
`e_ν` with `ν ⊢ n` are linearly independent in `N` variables.  Hence the statement for every
`N ≥ n` is equivalent to `R_k(e_μ) ∈ ℕ{e_ν}` in the ring of symmetric functions.  This
equivalence is a remark and is not formalized here. -/
theorem exponentDiv_esymmPart_ePositive_of_macdonaldInput {k n : ℕ}
    (hk : 0 < k) (hn : n ≤ N) (mu : (k * n).Partition)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N)
    (hrect : MacdonaldRootRectangles heig hne k) :
    ∃ c : n.Partition → ℕ,
      exponentDiv k (esymmPart (Fin N) ℤ mu) = ∑ nu, c nu • esymmPart (Fin N) ℤ nu := by
  have : NeZero k := ⟨hk.ne'⟩
  have : NeZero (k : ℚ) := ⟨Nat.cast_ne_zero.mpr hk.ne'⟩
  let _ : Algebra ℚ (CyclotomicField k ℚ) := CyclotomicField.algebra k ℚ
  have hζ := IsCyclotomicExtension.zeta_spec k ℚ (CyclotomicField k ℚ)
  exact exponentDiv_esymmPart_ePositive_of_root hk hn mu hζ heig hne
    (hrect (CyclotomicField k ℚ) _ hζ)

/-- **The partition-division theorem** in `N` variables, with Lemmas 7 and 8 discharged.

For `0 < k`, `n ≤ N` and `μ ⊢ k n`, `exponentDiv k (e_μ)` is a natural-number combination of
the `e_ν`, `ν ⊢ n`. The only remaining hypothesis is the rectangle values
`P_{k • 1^h}(x; ζ, ζ v) = e_h(x ^ k)` of the specialized Macdonald basis. -/
theorem exponentDiv_esymmPart_ePositive_of_rectangles {k n : ℕ}
    (hk : 0 < k) (hn : n ≤ N) (mu : (k * n).Partition)
    (hrect : MacdonaldRootRectangles Macdonald.macdonaldJointEigen
      (macdonaldBaseEvalNeZero N) k) :
    ∃ c : n.Partition → ℕ,
      exponentDiv k (esymmPart (Fin N) ℤ mu) = ∑ nu, c nu • esymmPart (Fin N) ℤ nu :=
  exponentDiv_esymmPart_ePositive_of_macdonaldInput hk hn mu
    Macdonald.macdonaldJointEigen (macdonaldBaseEvalNeZero N) hrect

/-! ### The rectangle values of the specialized basis -/

section RootRectangles

attribute [local instance] RingHom.ker_isPrime

variable {L : Type*} [Field L] [CharZero L]

/-- The specialized Macdonald basis vector is the specialization of a polynomial over the local
ring `O` at the kernel of `rootSpecialization ζ` whose image over `ℚ(q, t)` is `P_λ`. -/
theorem exists_lift_macdonaldRootBasis (ζ : L)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N)
    (lam : Nat.PartitionVector N) :
    ∃ Q : MvPolynomial (Fin N)
        (Localization.AtPrime (RingHom.ker (Macdonald.rootSpecialization ζ))),
      (macdonaldRootBasis ζ heig hne lam : MvPolynomial (Fin N) (RationalFunction L)) =
          map (Macdonald.specializationHom (Macdonald.rootSpecialization ζ)) Q ∧
        map (algebraMap _ (FractionRing (MvPolynomial (Fin 2) ℚ))) Q = macdonaldP lam :=
  ⟨_, coe_specializedBasis _ _ _ _ _ _ lam, Macdonald.map_regularLift _ _ _ lam⟩

/-- The specialized Macdonald basis vectors satisfy the first-operator eigenvalue equation at
`(ζ, ζ v)`, in numerator form. -/
theorem macdonaldNumerator_macdonaldRootBasis (ζ : L)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N)
    (lam : Nat.PartitionVector N) :
    macdonaldNumerator (constantRationalFunction ζ) (scaledVariableRationalFunction ζ)
        (macdonaldRootBasis ζ heig hne lam : MvPolynomial (Fin N) (RationalFunction L)) =
      macdonaldEigenvalue (constantRationalFunction ζ) (scaledVariableRationalFunction ζ) lam •
        (vandermonde N (RationalFunction L) *
          (macdonaldRootBasis ζ heig hne lam : MvPolynomial (Fin N) (RationalFunction L))) := by
  obtain ⟨Q, hQ, hQK⟩ := exists_lift_macdonaldRootBasis ζ heig hne lam
  have hιinj := Macdonald.algebraMap_localization_fractionRing_injective
    (Macdonald.rootSpecialization ζ)
  have hO : macdonaldNumerator
        (algebraMap (MvPolynomial (Fin 2) ℚ)
          (Localization.AtPrime (RingHom.ker (Macdonald.rootSpecialization ζ)))
          (MvPolynomial.X 0))
        (algebraMap (MvPolynomial (Fin 2) ℚ)
          (Localization.AtPrime (RingHom.ker (Macdonald.rootSpecialization ζ)))
          (MvPolynomial.X 1)) Q =
      macdonaldEigenvalue
        (algebraMap (MvPolynomial (Fin 2) ℚ)
          (Localization.AtPrime (RingHom.ker (Macdonald.rootSpecialization ζ)))
          (MvPolynomial.X 0))
        (algebraMap (MvPolynomial (Fin 2) ℚ)
          (Localization.AtPrime (RingHom.ker (Macdonald.rootSpecialization ζ)))
          (MvPolynomial.X 1)) lam • (vandermonde N _ * Q) := by
    apply MvPolynomial.map_injective _ hιinj
    rw [Macdonald.map_macdonaldNumerator, Macdonald.map_smul_eq_smul_map, map_mul,
      Macdonald.map_vandermonde, Macdonald.map_macdonaldEigenvalue, hQK,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact macdonaldNumerator_macdonaldP lam
  have hF := congrArg
    (MvPolynomial.map (Macdonald.specializationHom (Macdonald.rootSpecialization ζ))) hO
  rw [Macdonald.map_macdonaldNumerator, Macdonald.map_smul_eq_smul_map, map_mul,
    Macdonald.map_vandermonde, Macdonald.map_macdonaldEigenvalue,
    Macdonald.specializationHom_algebraMap, Macdonald.specializationHom_algebraMap,
    Macdonald.rootSpecialization_X_zero, Macdonald.rootSpecialization_X_one, ← map_mul,
    ← hQ] at hF
  exact hF

/-- The specialized Macdonald basis vectors are eigenvectors of the first Macdonald operator at
`(ζ, ζ v)`. -/
theorem macdonaldD_macdonaldRootBasis (ζ : L)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N)
    (lam : Nat.PartitionVector N) :
    macdonaldD (constantRationalFunction ζ) (scaledVariableRationalFunction ζ)
        (macdonaldRootBasis ζ heig hne lam) =
      macdonaldEigenvalue (constantRationalFunction ζ) (scaledVariableRationalFunction ζ) lam •
        macdonaldRootBasis ζ heig hne lam := by
  apply Subtype.ext
  apply vandermonde_mul_injective
  change vandermonde N (RationalFunction L) *
      (macdonaldD (constantRationalFunction ζ) (scaledVariableRationalFunction ζ)
        (macdonaldRootBasis ζ heig hne lam) : MvPolynomial (Fin N) (RationalFunction L)) =
    vandermonde N (RationalFunction L) *
      (macdonaldEigenvalue (constantRationalFunction ζ) (scaledVariableRationalFunction ζ) lam •
        (macdonaldRootBasis ζ heig hne lam : MvPolynomial (Fin N) (RationalFunction L)))
  rw [vandermonde_mul_macdonaldD, mul_smul_comm]
  exact macdonaldNumerator_macdonaldRootBasis ζ heig hne lam

/-- The specialized Macdonald basis is homogeneous: `P_λ(x; ζ, ζ v)` has degree `|λ|`. -/
theorem isHomogeneous_macdonaldRootBasis (ζ : L)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N)
    (lam : Nat.PartitionVector N) :
    (macdonaldRootBasis ζ heig hne lam : MvPolynomial (Fin N) (RationalFunction L)).IsHomogeneous
      (partitionVectorDegree lam) := by
  obtain ⟨Q, hQ, hQK⟩ := exists_lift_macdonaldRootBasis ζ heig hne lam
  have hιinj := Macdonald.algebraMap_localization_fractionRing_injective
    (Macdonald.rootSpecialization ζ)
  have hQhom : Q.IsHomogeneous (partitionVectorDegree lam) := by
    intro d hd
    apply isHomogeneous_macdonaldP lam
    rw [← hQK, MvPolynomial.coeff_map]
    exact (map_ne_zero_iff _ hιinj).mpr hd
  rw [hQ]
  exact hQhom.map _

/-- The specialized Macdonald basis is lex-unitriangular. -/
theorem isLexUnitriangular_macdonaldRootBasis (ζ : L)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N)
    (lam : Nat.PartitionVector N) :
    Macdonald.IsLexUnitriangular
      (macdonaldRootBasis ζ heig hne lam : MvPolynomial (Fin N) (RationalFunction L)) lam := by
  obtain ⟨Q, hQ, hQK⟩ := exists_lift_macdonaldRootBasis ζ heig hne lam
  have hιinj := Macdonald.algebraMap_localization_fractionRing_injective
    (Macdonald.rootSpecialization ζ)
  rw [hQ]
  exact (Macdonald.IsLexUnitriangular.of_map hιinj
    (hQK ▸ Macdonald.isLexUnitriangular_macdonaldP lam)).map _

/-- Span membership in the symmetric subalgebra, read in the polynomial ring. -/
theorem mem_span_symmetricMsymmVec_iff {F : Type*} [Field F]
    (S : Set (Nat.PartitionVector N)) (x : symmetricSubalgebra (Fin N) F) :
    x ∈ Submodule.span F (Macdonald.symmetricMsymmVec F '' S) ↔
      (x : MvPolynomial (Fin N) F) ∈ Submodule.span F (msymmVec F '' S) := by
  have hmap := Submodule.map_span (symmetricSubalgebra (Fin N) F).val.toLinearMap
    (Macdonald.symmetricMsymmVec F '' S)
  have himage : (symmetricSubalgebra (Fin N) F).val.toLinearMap ''
      (Macdonald.symmetricMsymmVec F '' S) = msymmVec F '' S := by
    rw [Set.image_image]
    rfl
  rw [himage] at hmap
  constructor
  · intro hx
    rw [← hmap]
    exact Submodule.mem_map_of_mem hx
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']

/-- The specialized Macdonald basis vector is `m_λ` plus lexicographically lower `m_μ` of the
same size. -/
theorem macdonaldRootBasis_sub_mem_span (ζ : L)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N)
    (lam : Nat.PartitionVector N) :
    macdonaldRootBasis ζ heig hne lam - Macdonald.symmetricMsymmVec (RationalFunction L) lam ∈
      Submodule.span (RationalFunction L)
        (Macdonald.symmetricMsymmVec (RationalFunction L) ''
          {mu | partitionVectorDegree mu = partitionVectorDegree lam ∧
            Macdonald.lexKey mu < Macdonald.lexKey lam}) := by
  rw [mem_span_symmetricMsymmVec_iff]
  have htri := isLexUnitriangular_macdonaldRootBasis ζ heig hne lam
  have hhom := isHomogeneous_macdonaldRootBasis ζ heig hne lam
  set p : MvPolynomial (Fin N) (RationalFunction L) :=
    (macdonaldRootBasis ζ heig hne lam : MvPolynomial (Fin N) (RationalFunction L)) with hp
  change p - msymmVec (RationalFunction L) lam ∈ _
  have hsym : (p - msymmVec (RationalFunction L) lam).IsSymmetric :=
    htri.isSymmetric.sub (msymmVec_isSymmetric _ lam)
  have hghom : (p - msymmVec (RationalFunction L) lam).IsHomogeneous
      (partitionVectorDegree lam) :=
    (homogeneousSubmodule (Fin N) (RationalFunction L) _).sub_mem hhom
      (isHomogeneous_msymmVec _ lam)
  refine hsym.mem_span_msymmVec fun mu hmu ↦ ⟨hghom.partitionVectorDegree_eq hmu, ?_⟩
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub,
    coeff_msymmVec_partitionVectorFinsupp] at hmu
  rcases lt_trichotomy (Macdonald.lexKey mu) (Macdonald.lexKey lam) with hlt | heq | hgt
  · exact hlt
  · have hmulam := Macdonald.lexKey_injective heq
    subst hmulam
    rw [htri.coeff_self] at hmu
    simp at hmu
  · have hne' : mu ≠ lam := fun h ↦ (lt_irrefl _ (h ▸ hgt))
    rw [htri.coeff_eq_zero_of_lt mu hgt] at hmu
    simp [hne'] at hmu

end RootRectangles

/-- **The rectangle values** of the specialized Macdonald basis: for every `0 < k`, every field
`L` of characteristic zero and every primitive `k`-th root of unity `ζ ∈ L`,
`P_{k • 1^h}(x; ζ, ζ v) = e_h(x ^ k)` for `1 ≤ h ≤ N`. -/
theorem macdonaldRootRectangles {k : ℕ} (hk : 0 < k)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N) :
    MacdonaldRootRectangles heig hne k := by
  intro L _ _ ζ hζ
  exact Macdonald.satisfiesRectangles_of_macdonaldD_eigenvectors ζ hζ hk
    (macdonaldRootBasis ζ heig hne) (macdonaldRootBasis_sub_mem_span ζ heig hne)
    (macdonaldD_macdonaldRootBasis ζ heig hne)

/-- **The partition-division theorem** in `N` variables.

For `0 < k`, `n ≤ N` and a partition `μ ⊢ k n`, the exponent division `R_k = exponentDiv k`
sends `e_μ` to a natural-number combination of the `e_ν`, `ν ⊢ n`.  There are no further
hypotheses: ledger Lemmas 7 and 8 and the rectangle values are proved
(`Macdonald.macdonaldJointEigen`, `macdonaldBaseEvalNeZero`, `macdonaldRootRectangles`).

**Remark (relation to symmetric functions).**  `exponentDiv k` is the operator `R_k` restricted
to `N` variables: it keeps the monomials whose exponents are all divisible by `k` and divides
those exponents by `k`.  Restriction to `N` variables commutes with `R_k`, and for `N ≥ n` the
`e_ν` with `ν ⊢ n` are linearly independent in `N` variables.  Hence the statement for every
`N ≥ n` is equivalent to `R_k(e_μ) ∈ ℕ{e_ν}` in the ring of symmetric functions.  This
equivalence is a remark and is not formalized here. -/
theorem exponentDiv_esymmPart_ePositive {k n : ℕ} (hk : 0 < k) (hn : n ≤ N)
    (mu : (k * n).Partition) :
    ∃ c : n.Partition → ℕ,
      exponentDiv k (esymmPart (Fin N) ℤ mu) = ∑ nu, c nu • esymmPart (Fin N) ℤ nu :=
  exponentDiv_esymmPart_ePositive_of_rectangles hk hn mu
    (macdonaldRootRectangles hk _ _)

end PartitionDivision
