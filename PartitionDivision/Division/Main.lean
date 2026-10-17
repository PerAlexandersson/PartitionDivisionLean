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

The Macdonald inputs that are still being proved elsewhere are separate, named hypotheses:

* `Macdonald.MacdonaldJointEigen` (ledger Lemma 7);
* `MacdonaldBaseEvalNeZero` (ledger Lemma 8);
* `MacdonaldRootRectangles` (the rectangle values of the specialized basis).
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
theorem exists_nat_esymm_expansion_exponentDiv_esymmPart_of_root {k n : ℕ} (hk : 0 < k)
    (hn : n ≤ N) (mu : (k * n).Partition) {L : Type*} [Field L] [CharZero L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ k)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N)
    (hrect : SatisfiesRectangles (macdonaldRootBasis ζ heig hne) k) :
    ∃ c : n.Partition → ℕ,
      exponentDiv k (esymmPart (Fin N) ℤ mu) = ∑ nu, c nu • esymmPart (Fin N) ℤ nu :=
  exists_nat_esymm_expansion_of_pieri_at_root_of_unity hk hn mu hζ
    (macdonaldRootBasis ζ heig hne) (satisfiesPieri_macdonaldRootBasis ζ heig hne)
    (macdonaldRootBasis_zero ζ heig hne) hrect

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
theorem exists_nat_esymm_expansion_exponentDiv_esymmPart {k n : ℕ} (hk : 0 < k) (hn : n ≤ N)
    (mu : (k * n).Partition)
    (heig : Macdonald.MacdonaldJointEigen (N := N)) (hne : MacdonaldBaseEvalNeZero N)
    (hrect : MacdonaldRootRectangles heig hne k) :
    ∃ c : n.Partition → ℕ,
      exponentDiv k (esymmPart (Fin N) ℤ mu) = ∑ nu, c nu • esymmPart (Fin N) ℤ nu := by
  have : NeZero k := ⟨hk.ne'⟩
  have : NeZero (k : ℚ) := ⟨Nat.cast_ne_zero.mpr hk.ne'⟩
  let _ : Algebra ℚ (CyclotomicField k ℚ) := CyclotomicField.algebra k ℚ
  have hζ := IsCyclotomicExtension.zeta_spec k ℚ (CyclotomicField k ℚ)
  exact exists_nat_esymm_expansion_exponentDiv_esymmPart_of_root hk hn mu hζ heig hne
    (hrect (CyclotomicField k ℚ) _ hζ)

end PartitionDivision
