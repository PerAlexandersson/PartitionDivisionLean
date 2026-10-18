/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Division.Main

/-!
# The walk formula for the partition-division coefficients

Fix `0 < k`.  The vertices are the `k`-restricted partition vectors `KRestricted N k`.  An edge of
size `r` out of a vertex `λ` is a legal vertical strip `δ` of size `r` on `λ`: writing
`λ + δ = τ + k • ξ` with `τ` restricted (`decompositionEquiv`), the edge goes from `λ` to `τ`, has
label the difference vector of `ξ` (the column multiplicities of `ξ`), and has the explicit weight
`walkWeight k λ δ`.  This weight is a product over the contributing row pairs of the values of
`rootRatioWeight`: it is the value at `v = 1` of the Pieri coefficient at `q = ζ`, `t = ζ v`.

`walkFollow` follows a sequence of strips with prescribed sizes from a vertex and records the end
vertex, the total label and the product of the weights.

The main theorem `natCast_mul_eq_sum_closedWalks` is the walk formula: for `μ ⊢ k n`, `n ≤ N`, any
ordering `l` of the parts of `μ`, the unique natural-number coefficients
`R_k(e_μ) = Σ_ν c_ν e_ν` satisfy

  `k ^ N * c_ν = Σ_{closed walks W with step sizes l and label mult(ν)} wt(W)`,

where `mult(ν)` records the multiplicity of each part size of `ν`.

The proof places the explicit weights in the transition matrices `walkMatrix` and reruns the
specialization argument of `Division.RootOfUnity` with them; the trace of their product is then
`k ^ N` times the elementary expansion, and expanding the trace gives the sum over closed walks.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace PartitionDivision

open MvPolynomial Nat.PartitionVector Nat.PartitionVector.Pieri

variable {N k : ℕ}

/-! ### Explicit weights -/

/-- The weight of one contributing row pair: the value at `v = 1` of its two grouped root-of-unity
quotients. -/
def pairWalkWeight (k : ℕ) (lam : Nat.PartitionVector N) (ij : Fin N × Fin N) : ℚ≥0 :=
  rootRatioWeight k (rowDifference lam ij + rowDistance ij - 1) (rowDistance ij - 1)
      (rowDistance ij) *
    rootRatioWeight k (rowDifference lam ij + rowDistance ij) (rowDistance ij + 1)
      (rowDistance ij)

/-- The weight of the edge given by a strip `δ` on `λ`: the value at `v = 1` of the Pieri
coefficient `ψ'` at `q = ζ`, `t = ζ v`, for a primitive `k`-th root of unity `ζ`. -/
def walkWeight (k : ℕ) (lam : Nat.PartitionVector N) (δ : Strip N) : ℚ≥0 :=
  ∏ ij ∈ rowPairs δ, pairWalkWeight k lam ij

section Presentation

variable {L : Type*} [Field L]

/-- A polynomial presentation of the root-of-unity binomial quotients: `(1 - X^n)/(1 - X)` when
`k ∣ c`, and the binomial `1 - ζ^c X^n` otherwise. -/
def rootRatioPoly (ζ : L) (k c n : ℕ) : Polynomial L := by
  classical
  exact if k ∣ c then ∑ i ∈ Finset.range n, Polynomial.X ^ i else rootBinomial ζ c n

theorem rootBinomial_mul_rootRatioPoly {ζ : L} (hζ : IsPrimitiveRoot ζ k) (c n m : ℕ) :
    rootBinomial ζ c n * rootRatioPoly ζ k c m = rootBinomial ζ c m * rootRatioPoly ζ k c n := by
  classical
  unfold rootRatioPoly
  by_cases hc : k ∣ c
  · have hpow : ζ ^ c = 1 := (hζ.pow_eq_one_iff_dvd c).mpr hc
    simp only [hc, ↓reduceIte, rootBinomial, hpow, map_one, one_mul]
    rw [← geom_sum_mul_neg, ← geom_sum_mul_neg]
    ring
  · simp only [hc, ↓reduceIte]
    ring

theorem eval_one_rootRatioPoly (ζ : L) (k c n : ℕ) :
    (rootRatioPoly ζ k c n).eval 1 = if k ∣ c then (n : L) else 1 - ζ ^ c := by
  classical
  unfold rootRatioPoly
  by_cases hc : k ∣ c
  · simp [hc]
  · simp [hc, rootBinomial]

theorem eval_one_rootRatioPoly_ne_zero [CharZero L] {ζ : L} (hζ : IsPrimitiveRoot ζ k)
    (c : ℕ) {m : ℕ} (hm : 0 < m) : (rootRatioPoly ζ k c m).eval 1 ≠ 0 := by
  rw [eval_one_rootRatioPoly]
  split_ifs with hc
  · exact Nat.cast_ne_zero.mpr hm.ne'
  · have hpow : ζ ^ c ≠ 1 := (hζ.pow_eq_one_iff_dvd c).not.mpr hc
    exact sub_ne_zero.mpr (Ne.symm hpow)

theorem eval_one_rootRatioPoly_div [CharZero L] {ζ : L} (hζ : IsPrimitiveRoot ζ k)
    (c n m : ℕ) :
    (rootRatioPoly ζ k c n).eval 1 / (rootRatioPoly ζ k c m).eval 1 =
      (rootRatioWeight k c n m : L) := by
  rw [eval_one_rootRatioPoly, eval_one_rootRatioPoly, rootRatioWeight]
  split_ifs with hc
  · simp
  · have hpow : ζ ^ c ≠ 1 := (hζ.pow_eq_one_iff_dvd c).not.mpr hc
    rw [NNRat.cast_one]
    exact div_self (sub_ne_zero.mpr (Ne.symm hpow))

/-- The numerator of the presentation of a row-pair quotient. -/
def pairNumPoly (ζ : L) (k : ℕ) (lam : Nat.PartitionVector N) (ij : Fin N × Fin N) :
    Polynomial L :=
  rootRatioPoly ζ k (rowDifference lam ij + rowDistance ij - 1) (rowDistance ij - 1) *
    rootRatioPoly ζ k (rowDifference lam ij + rowDistance ij) (rowDistance ij + 1)

/-- The denominator of the presentation of a row-pair quotient. -/
def pairDenPoly (ζ : L) (k : ℕ) (lam : Nat.PartitionVector N) (ij : Fin N × Fin N) :
    Polynomial L :=
  rootRatioPoly ζ k (rowDifference lam ij + rowDistance ij - 1) (rowDistance ij) *
    rootRatioPoly ζ k (rowDifference lam ij + rowDistance ij) (rowDistance ij)

theorem pairNum_mul_pairDenPoly {ζ : L} (hζ : IsPrimitiveRoot ζ k)
    {lam : Nat.PartitionVector N} {δ : Strip N} (hδ : IsLegal lam δ) {ij : Fin N × Fin N}
    (hij : ij ∈ rowPairs δ) :
    pairNum lam (Polynomial.C ζ) (Polynomial.C ζ * Polynomial.X) ij * pairDenPoly ζ k lam ij =
      pairDen lam (Polynomial.C ζ) (Polynomial.C ζ * Polynomial.X) ij *
        pairNumPoly ζ k lam ij := by
  rw [pairNum_C_C_mul_X ζ hδ hij, pairDen_C_C_mul_X ζ hδ hij, pairNumPoly, pairDenPoly]
  set c₁ := rowDifference lam ij + rowDistance ij - 1
  set c₂ := rowDifference lam ij + rowDistance ij
  set m := rowDistance ij
  have h1 := rootBinomial_mul_rootRatioPoly hζ c₁ (m - 1) m
  have h2 := rootBinomial_mul_rootRatioPoly hζ c₂ (m + 1) m
  linear_combination (rootBinomial ζ c₂ (m + 1) * rootRatioPoly ζ k c₂ m) * h1 +
    (rootBinomial ζ c₁ m * rootRatioPoly ζ k c₁ (m - 1)) * h2

/-- The numerator of the explicit presentation of the specialized Pieri coefficient. -/
def walkNumPoly (ζ : L) (k : ℕ) (lam : Nat.PartitionVector N) (δ : Strip N) : Polynomial L :=
  ∏ ij ∈ rowPairs δ, pairNumPoly ζ k lam ij

/-- The denominator of the explicit presentation of the specialized Pieri coefficient. -/
def walkDenPoly (ζ : L) (k : ℕ) (lam : Nat.PartitionVector N) (δ : Strip N) : Polynomial L :=
  ∏ ij ∈ rowPairs δ, pairDenPoly ζ k lam ij

theorem pieriNum_mul_walkDenPoly {ζ : L} (hζ : IsPrimitiveRoot ζ k)
    {lam : Nat.PartitionVector N} {δ : Strip N} (hδ : IsLegal lam δ) :
    pieriNum lam δ (Polynomial.C ζ) (Polynomial.C ζ * Polynomial.X) * walkDenPoly ζ k lam δ =
      pieriDen lam δ (Polynomial.C ζ) (Polynomial.C ζ * Polynomial.X) *
        walkNumPoly ζ k lam δ := by
  rw [pieriNum, pieriDen, walkDenPoly, walkNumPoly, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun ij hij ↦ pairNum_mul_pairDenPoly hζ hδ hij

theorem eval_one_walkDenPoly_ne_zero [CharZero L] {ζ : L} (hζ : IsPrimitiveRoot ζ k)
    (lam : Nat.PartitionVector N) (δ : Strip N) : (walkDenPoly ζ k lam δ).eval 1 ≠ 0 := by
  rw [walkDenPoly, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro ij hij
  rw [pairDenPoly, Polynomial.eval_mul]
  exact mul_ne_zero (eval_one_rootRatioPoly_ne_zero hζ _ (rowDistance_pos hij))
    (eval_one_rootRatioPoly_ne_zero hζ _ (rowDistance_pos hij))

theorem eval_one_walkNumPoly_div [CharZero L] {ζ : L} (hζ : IsPrimitiveRoot ζ k)
    (lam : Nat.PartitionVector N) (δ : Strip N) :
    (walkNumPoly ζ k lam δ).eval 1 / (walkDenPoly ζ k lam δ).eval 1 =
      (walkWeight k lam δ : L) := by
  rw [walkNumPoly, walkDenPoly, Polynomial.eval_prod, Polynomial.eval_prod,
    ← Finset.prod_div_distrib, walkWeight, NNRat.cast_prod]
  refine Finset.prod_congr rfl fun ij hij ↦ ?_
  rw [pairNumPoly, pairDenPoly, Polynomial.eval_mul, Polynomial.eval_mul, mul_div_mul_comm,
    eval_one_rootRatioPoly_div hζ, eval_one_rootRatioPoly_div hζ, pairWalkWeight,
    NNRat.cast_mul]

end Presentation

/-! ### The regular lift of the specialized Pieri coefficient -/

section Regular

variable {L : Type*} [Field L] [CharZero L]

theorem walkDenPoly_mem_primeCompl {z : L} (hz : IsPrimitiveRoot z k)
    (lam : Nat.PartitionVector N) (δ : Strip N) :
    walkDenPoly z k lam δ ∈ (evalOneIdeal L).primeCompl := fun hmem ↦
  eval_one_walkDenPoly_ne_zero hz lam δ hmem

/-- The specialized Pieri coefficient as an element of the local ring at `v = 1`, given by the
explicit presentation `walkNumPoly / walkDenPoly`. -/
def walkRegularCoeff {z : L} (hz : IsPrimitiveRoot z k) (lam : Nat.PartitionVector N)
    (δ : Strip N) : RegularAtOne L :=
  IsLocalization.mk' (RegularAtOne L) (walkNumPoly z k lam δ)
    ⟨walkDenPoly z k lam δ, walkDenPoly_mem_primeCompl hz lam δ⟩

/-- On a legal strip, the regular lift maps to the specialized Pieri coefficient. -/
theorem regularAtOneToFractionRing_walkRegularCoeff {z : L} (hz : IsPrimitiveRoot z k)
    {lam : Nat.PartitionVector N} {δ : Strip N} (hδ : IsLegal lam δ) :
    regularAtOneToFractionRing L (walkRegularCoeff hz lam δ) =
      pieriCoefficient (constantRationalFunction z) (scaledVariableRationalFunction z)
        lam δ := by
  let g : Polynomial L →+* RationalFunction L := algebraMap (Polynomial L) (RationalFunction L)
  have hdenPoly := pieriDen_C_C_mul_X_ne_zero z lam δ
  have hden : pieriDen lam δ (g (Polynomial.C z)) (g (Polynomial.C z * Polynomial.X)) ≠ 0 := by
    rw [← map_pieriDen g, ← map_zero g]
    exact (IsFractionRing.injective (Polynomial L) (RationalFunction L)).ne hdenPoly
  have hcross := congrArg g (pieriNum_mul_walkDenPoly hz hδ)
  rw [map_mul, map_mul, map_pieriNum, map_pieriDen] at hcross
  rw [walkRegularCoeff, regularAtOneToFractionRing, IsLocalization.lift_mk'_spec]
  change g (walkNumPoly z k lam δ) = g (walkDenPoly z k lam δ) *
    pieriCoefficient (g (Polynomial.C z)) (g (Polynomial.C z * Polynomial.X)) lam δ
  rw [pieriCoefficient, ← mul_div_assoc, eq_div_iff hden]
  simpa only [mul_comm] using hcross.symm

/-- The regular lift evaluates at `v = 1` to the explicit walk weight. -/
theorem regularAtOneEval_walkRegularCoeff {z : L} (hz : IsPrimitiveRoot z k)
    (lam : Nat.PartitionVector N) (δ : Strip N) :
    regularAtOneEval L (walkRegularCoeff hz lam δ) = (walkWeight k lam δ : L) := by
  rw [walkRegularCoeff, regularAtOneEval, IsLocalization.lift_mk'_spec]
  change (walkNumPoly z k lam δ).eval 1 = (walkDenPoly z k lam δ).eval 1 * (walkWeight k lam δ : L)
  rw [(div_eq_iff (eval_one_walkDenPoly_ne_zero hz lam δ)).mp
    (eval_one_walkNumPoly_div hz lam δ), mul_comm]

end Regular

/-! ### Transition matrices -/

/-- The target vertex of the edge given by a strip. -/
def walkTarget (hk : 0 < k) (lam : KRestricted N k) (δ : Strip N) : KRestricted N k :=
  (decompositionEquiv N k hk (addStrip lam.1 δ)).1

/-- The label of the edge given by a strip: the difference vector (column multiplicities) of the
quotient part `ξ` of `λ + δ = τ + k • ξ`. -/
def walkLabel (hk : 0 < k) (lam : KRestricted N k) (δ : Strip N) : Fin N →₀ ℕ :=
  differenceFinsupp (decompositionEquiv N k hk (addStrip lam.1 δ)).2

open Classical in
/-- The transition matrix of the walks of size `r`, with the explicit weights; the entry at
`(τ, λ)` sums over the edges from `λ` to `τ`. -/
def walkMatrix (hk : 0 < k) (r : ℕ) :
    Matrix (KRestricted N k) (KRestricted N k) (MvPolynomial (Fin N) ℚ) :=
  fun tau lam ↦ ∑ δ : Strip N,
    if IsLegal lam.1 δ ∧ stripWeight δ = r ∧ walkTarget hk lam δ = tau then
      MvPolynomial.C (walkWeight k lam.1 δ : ℚ) * monomial (walkLabel hk lam δ) 1
    else 0

open Classical in
/-- The transition matrix over the local ring at `v = 1`. -/
def walkRegularMatrix {L : Type*} [Field L] [CharZero L] {z : L} (hz : IsPrimitiveRoot z k)
    (hk : 0 < k) (r : ℕ) :
    Matrix (KRestricted N k) (KRestricted N k) (MvPolynomial (Fin N) (RegularAtOne L)) :=
  fun tau lam ↦ ∑ δ : Strip N,
    if IsLegal lam.1 δ ∧ stripWeight δ = r ∧ walkTarget hk lam δ = tau then
      MvPolynomial.C (walkRegularCoeff hz lam.1 δ) * monomial (walkLabel hk lam δ) 1
    else 0

/-- The entries of the walk matrices have nonnegative coefficients. -/
theorem walkMatrix_hasNonnegCoeffs (hk : 0 < k) (r : ℕ) (tau lam : KRestricted N k) :
    (walkMatrix hk r tau lam).HasNonnegCoeffs := by
  classical
  apply MvPolynomial.HasNonnegCoeffs.finset_sum
  intro δ _
  split_ifs
  · apply MvPolynomial.HasNonnegCoeffs.mul (MvPolynomial.HasNonnegCoeffs.C (by positivity))
    intro d
    rw [coeff_monomial]
    split_ifs <;> norm_num
  · exact MvPolynomial.HasNonnegCoeffs.zero

/-- **Trace identity for the walk matrices.**  For a symmetric basis satisfying the Pieri and
rectangle identities at a primitive root of unity, the trace of the product of the walk
matrices, evaluated at the elementary symmetric polynomials, is `k ^ N` times the exponent
division of the corresponding product of elementary symmetric polynomials. -/
theorem aeval_trace_walkMatrix_of_basis (hk : 0 < k) {L : Type*} [Field L] [CharZero L]
    {z : L} (hz : IsPrimitiveRoot z k)
    (P : Module.Basis (Nat.PartitionVector N) (RationalFunction L)
      (symmetricSubalgebra (Fin N) (RationalFunction L)))
    (hPieri : SatisfiesPieri P (constantRationalFunction z) (scaledVariableRationalFunction z))
    (hzero : P 0 = 1) (hrectangles : SatisfiesRectangles P k) (l : List ℕ) :
    aeval (fun i : Fin N ↦ esymm (Fin N) ℚ (i + 1))
        (Matrix.trace ((l.map (walkMatrix hk)).reverse.prod)) =
      (k ^ N : ℚ) • exponentDiv k ((l.map fun r ↦ esymm (Fin N) ℚ r).prod) := by
  classical
  let qToRegular : ℚ →+* RegularAtOne L :=
    (algebraMap (Polynomial L) (RegularAtOne L)).comp
      ((Polynomial.C : L →+* Polynomial L).comp (Rat.castHom L))
  let _ : Algebra ℚ (RegularAtOne L) := qToRegular.toAlgebra
  let _ : Algebra (RegularAtOne L) (RationalFunction L) :=
    (regularAtOneToFractionRing L).toAlgebra
  let _ : Algebra ℚ L := (Rat.castHom L).toAlgebra
  let baseToFraction : L →+* RationalFunction L :=
    (algebraMap (Polynomial L) (RationalFunction L)).comp Polynomial.C
  have hbase : Function.Injective baseToFraction :=
    (IsFractionRing.injective (Polynomial L) (RationalFunction L)).comp Polynomial.C_injective
  let _ : CharZero (RationalFunction L) := charZero_of_injective_ringHom hbase
  have hzFraction : IsPrimitiveRoot (constantRationalFunction z) k :=
    hz.map_of_injective hbase
  let ev : RegularAtOne L →ₐ[ℚ] L :=
    { __ := regularAtOneEval L
      commutes' := fun q ↦ by
        change regularAtOneEval L (algebraMap (Polynomial L) (RegularAtOne L)
          (Polynomial.C ((Rat.castHom L) q))) = (Rat.castHom L) q
        rw [regularAtOneEval, IsLocalization.lift_eq]
        simp }
  have hF := trace_reverse_list_prod_eq_exponentFilter hk hzFraction (card_kRestricted N k)
    (zeroKRestricted hk) (restrictedBasisPolynomial P)
    (restrictedBasisPolynomial_zero P hzero hk)
    (pieriTransitionMatrix hk (constantRationalFunction z) (scaledVariableRationalFunction z))
    (fun r tau ↦ pieriTransitionMatrix_mul P _ _ hk hzFraction.pow_eq_one hPieri hzero
      hrectangles r tau) l
  have hMAF : ∀ r, pieriTransitionMatrix (N := N) hk (constantRationalFunction z)
      (scaledVariableRationalFunction z) r =
        (walkRegularMatrix hz hk r).map
          (MvPolynomial.map (algebraMap (RegularAtOne L) (RationalFunction L))) := by
    intro r
    apply Matrix.ext
    intro tau lam
    change pieriTransitionPolynomial hk (constantRationalFunction z)
        (scaledVariableRationalFunction z) r tau lam =
      MvPolynomial.map (regularAtOneToFractionRing L) (walkRegularMatrix hz hk r tau lam)
    rw [pieriTransitionPolynomial, walkRegularMatrix, map_sum]
    refine Finset.sum_congr rfl fun δ _ ↦ ?_
    by_cases hsel : IsLegal lam.1 δ ∧ stripWeight δ = r ∧ walkTarget hk lam δ = tau
    · have hsel' : IsLegal lam.1 δ ∧ stripWeight δ = r ∧
          (decompositionEquiv N k hk (addStrip lam.1 δ)).1 = tau := hsel
      simp only [hsel, hsel', and_self, ↓reduceIte, map_mul, map_C, map_monomial, map_one]
      rw [regularAtOneToFractionRing_walkRegularCoeff hz hsel.1, differenceMonomial,
        walkLabel]
    · have hsel' : ¬(IsLegal lam.1 δ ∧ stripWeight δ = r ∧
          (decompositionEquiv N k hk (addStrip lam.1 δ)).1 = tau) := hsel
      simp only [hsel, hsel', ↓reduceIte, map_zero]
  have hMAG : ∀ r, (walkRegularMatrix hz hk r).map (MvPolynomial.map ev.toRingHom) =
      (walkMatrix (N := N) hk r).map (MvPolynomial.map (algebraMap ℚ L)) := by
    intro r
    apply Matrix.ext
    intro tau lam
    simp only [Matrix.map_apply, walkRegularMatrix, walkMatrix, map_sum]
    refine Finset.sum_congr rfl fun δ _ ↦ ?_
    split_ifs
    · simp only [map_mul, map_C, map_monomial, map_one]
      congr 2
      change regularAtOneEval L (walkRegularCoeff hz lam.1 δ) = (Rat.castHom L) _
      rw [regularAtOneEval_walkRegularCoeff]
      simp
    · simp
  have hℚ := trace_identity_over_rat_of_base_change (A := RegularAtOne L)
    (F := RationalFunction L) (G := L)
    (by
      change Function.Injective (regularAtOneToFractionRing L)
      exact regularAtOneToFractionRing_injective L)
    ev _ (walkRegularMatrix hz hk) (walkMatrix hk) hMAF hMAG l hF
  have hT := (trace_list_prod_hasNonnegCoeffs_and_aeval_eq (walkMatrix hk)
    (walkMatrix_hasNonnegCoeffs hk) l hℚ).2
  have h := aeval_esymm_eq_smul_exponentDiv_of_aeval_expand_eq (N := N) (k := k) (q := k ^ N)
    hk (by simpa only [Nat.cast_pow] using hT)
  simpa only [Nat.cast_pow] using h

/-- **Trace identity for the walk matrices**, from the specialized Macdonald basis at a primitive
`k`-th root of unity in `ℚ(ζ_k)`. -/
theorem aeval_trace_walkMatrix (hk : 0 < k) (l : List ℕ) :
    aeval (fun i : Fin N ↦ esymm (Fin N) ℚ (i + 1))
        (Matrix.trace ((l.map (walkMatrix hk)).reverse.prod)) =
      (k ^ N : ℚ) • exponentDiv k ((l.map fun r ↦ esymm (Fin N) ℚ r).prod) := by
  have : NeZero k := ⟨hk.ne'⟩
  have : NeZero (k : ℚ) := ⟨Nat.cast_ne_zero.mpr hk.ne'⟩
  let _ : Algebra ℚ (CyclotomicField k ℚ) := CyclotomicField.algebra k ℚ
  have hζ := IsCyclotomicExtension.zeta_spec k ℚ (CyclotomicField k ℚ)
  exact aeval_trace_walkMatrix_of_basis hk hζ
    (macdonaldRootBasis _ Macdonald.macdonaldJointEigen (macdonaldBaseEvalNeZero N))
    (satisfiesPieri_macdonaldRootBasis _ _ _) (macdonaldRootBasis_zero _ _ _)
    (macdonaldRootRectangles hk _ _ (CyclotomicField k ℚ) _ hζ) l

/-! ### Reading off the elementary coefficients -/

/-- The multiplicity vector of a partition: its value at `i` is the number of parts equal to
`i + 1`.  The monomial `u ^ partitionMultiplicity N ν` corresponds to `e_ν` under `u_i ↦ e_{i+1}`.
-/
def partitionMultiplicity (N : ℕ) {n : ℕ} (nu : n.Partition) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ nu.parts.count (i.val + 1)

@[simp]
theorem partitionMultiplicity_apply {n : ℕ} (nu : n.Partition) (i : Fin N) :
    partitionMultiplicity N nu i = nu.parts.count (i.val + 1) := by
  simp [partitionMultiplicity]

/-- In at least `n` variables, distinct partitions of `n` have distinct multiplicity vectors. -/
theorem partitionMultiplicity_injective {n : ℕ} (hn : n ≤ N) :
    Function.Injective (partitionMultiplicity N (n := n)) := by
  intro nu nu' h
  apply Nat.Partition.ext
  rw [Multiset.ext]
  intro m
  by_cases hm0 : m = 0
  · subst hm0
    rw [Multiset.count_eq_zero.mpr fun h ↦ (nu.parts_pos h).ne' rfl,
      Multiset.count_eq_zero.mpr fun h ↦ (nu'.parts_pos h).ne' rfl]
  by_cases hmN : m ≤ N
  · have hi := congrArg (fun d : Fin N →₀ ℕ ↦ d ⟨m - 1, by lia⟩) h
    simp only [partitionMultiplicity_apply] at hi
    have hm : m - 1 + 1 = m := by lia
    rwa [hm] at hi
  · rw [Multiset.count_eq_zero.mpr fun h ↦ hmN ((nu.le_of_mem_parts h).trans hn),
      Multiset.count_eq_zero.mpr fun h ↦ hmN ((nu'.le_of_mem_parts h).trans hn)]

/-- The monomial of the multiplicity vector evaluates to `e_ν`. -/
theorem aeval_esymm_monomial_partitionMultiplicity {n : ℕ} (hn : n ≤ N) (nu : n.Partition)
    (a : ℚ) :
    aeval (fun i : Fin N ↦ esymm (Fin N) ℚ (i + 1)) (monomial (partitionMultiplicity N nu) a) =
      a • esymmPart (Fin N) ℚ nu := by
  classical
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Algebra.smul_def]
  congr 1
  let e : Fin N ↪ ℕ := ⟨fun i ↦ i.val + 1, fun a b h ↦ Fin.ext (by simpa using h)⟩
  have hsub : nu.parts.toFinset ⊆ (Finset.univ : Finset (Fin N)).map e := by
    intro m hm
    rw [Multiset.mem_toFinset] at hm
    have h1 := nu.parts_pos hm
    have h2 := (nu.le_of_mem_parts hm).trans hn
    rw [Finset.mem_map]
    exact ⟨⟨m - 1, by lia⟩, Finset.mem_univ _, by change m - 1 + 1 = m; lia⟩
  rw [esymmPart, Finset.prod_multiset_map_count, Finset.prod_subset hsub, Finset.prod_map]
  · rfl
  · intro m _ hm
    rw [Multiset.mem_toFinset] at hm
    rw [Multiset.count_eq_zero.mpr hm, pow_zero]

/-- **Coefficients of the trace.**  If `R_k(e_μ) = Σ_ν c_ν e_ν` over `ℤ`, then the coefficient of
`u ^ mult(ν)` in the trace of the product of the walk matrices, taken along any ordering of the
parts of `μ`, is `k ^ N * c_ν`. -/
theorem coeff_trace_walkMatrix (hk : 0 < k) {n : ℕ} (hn : n ≤ N) (mu : (k * n).Partition)
    (l : List ℕ) (hl : (l : Multiset ℕ) = mu.parts) (c : n.Partition → ℕ)
    (hc : exponentDiv k (esymmPart (Fin N) ℤ mu) = ∑ nu, c nu • esymmPart (Fin N) ℤ nu)
    (nu : n.Partition) :
    (Matrix.trace ((l.map (walkMatrix hk)).reverse.prod)).coeff (partitionMultiplicity N nu) =
      ((k ^ N * c nu : ℕ) : ℚ) := by
  classical
  have hcℚ : exponentDiv k (esymmPart (Fin N) ℚ mu) =
      ∑ nu, (c nu : ℚ) • esymmPart (Fin N) ℚ nu := by
    have h := congrArg (MvPolynomial.map (Int.castRingHom ℚ)) hc
    rw [map_exponentDiv, map_esymmPart, map_sum] at h
    rw [h]
    refine Finset.sum_congr rfl fun nu _ ↦ ?_
    rw [map_nsmul, map_esymmPart, Nat.cast_smul_eq_nsmul]
  have hprod : (l.map fun r ↦ esymm (Fin N) ℚ r).prod = esymmPart (Fin N) ℚ mu := by
    rw [esymmPart, ← hl, Multiset.map_coe, Multiset.prod_coe]
  set T := Matrix.trace ((l.map (walkMatrix hk)).reverse.prod) with hTdef
  let Q : MvPolynomial (Fin N) ℚ :=
    ∑ nu, monomial (partitionMultiplicity N nu) ((k ^ N : ℚ) * c nu)
  have hTQ : T = Q := by
    apply esymmAlgHom_fin_injective ℚ le_rfl
    apply Subtype.ext
    simp only [esymmAlgHom_apply]
    rw [hTdef, aeval_trace_walkMatrix hk l, hprod, hcℚ, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun nu _ ↦ ?_
    rw [aeval_esymm_monomial_partitionMultiplicity hn, smul_smul]
  rw [hTQ, coeff_sum]
  simp only [coeff_monomial, (partitionMultiplicity_injective hn).eq_iff, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  push_cast
  ring

/-! ### Closed walks -/

open Classical in
/-- Follow a sequence of strips `ds` with prescribed sizes `l` from the vertex `λ`.  The result is
`none` unless every strip is legal on the current vertex and has the prescribed size; otherwise it
is the end vertex, the total label, and the product of the edge weights. -/
def walkFollow (hk : 0 < k) : (l : List ℕ) → (Fin l.length → Strip N) → KRestricted N k →
    Option (KRestricted N k × (Fin N →₀ ℕ) × ℚ≥0)
  | [], _, lam => some (lam, 0, 1)
  | r :: l, ds, lam =>
    if IsLegal lam.1 (ds ⟨0, Nat.succ_pos _⟩) ∧ stripWeight (ds ⟨0, Nat.succ_pos _⟩) = r then
      (walkFollow hk l (fun i ↦ ds i.succ) (walkTarget hk lam (ds ⟨0, Nat.succ_pos _⟩))).map
        fun x ↦ (x.1, walkLabel hk lam (ds ⟨0, Nat.succ_pos _⟩) + x.2.1,
          walkWeight k lam.1 (ds ⟨0, Nat.succ_pos _⟩) * x.2.2)
    else none

theorem walkFollow_nil (hk : 0 < k) (ds : Fin 0 → Strip N) (lam : KRestricted N k) :
    walkFollow hk [] ds lam = some (lam, 0, 1) :=
  rfl

open Classical in
theorem walkFollow_cons (hk : 0 < k) (r : ℕ) (l : List ℕ) (δ : Strip N)
    (ds : Fin l.length → Strip N) (lam : KRestricted N k) :
    walkFollow hk (r :: l) (Fin.cons δ ds) lam =
      if IsLegal lam.1 δ ∧ stripWeight δ = r then
        (walkFollow hk l ds (walkTarget hk lam δ)).map
          fun x ↦ (x.1, walkLabel hk lam δ + x.2.1, walkWeight k lam.1 δ * x.2.2)
      else none := by
  classical
  rw [walkFollow]
  have h0 : (Fin.cons δ ds : Fin (l.length + 1) → Strip N) ⟨0, Nat.succ_pos _⟩ = δ :=
    rfl
  have hs : (fun i : Fin l.length ↦ (Fin.cons δ ds : Fin (l.length + 1) → Strip N) i.succ) =
      ds := funext fun i ↦ rfl
  simp only [h0, hs]

/-- The walk generating polynomial of a sequence of strips ending at `τ`. -/
private theorem elim_map_walk (tau : KRestricted N k) (lab : Fin N →₀ ℕ) (w : ℚ≥0)
    (o : Option (KRestricted N k × (Fin N →₀ ℕ) × ℚ≥0)) :
    (o.map fun x ↦ (x.1, lab + x.2.1, w * x.2.2)).elim 0
        (fun x ↦ if x.1 = tau then MvPolynomial.C (x.2.2 : ℚ) * monomial x.2.1 1 else 0) =
      (MvPolynomial.C (w : ℚ) * monomial lab 1) *
        o.elim 0 (fun x ↦ if x.1 = tau then MvPolynomial.C (x.2.2 : ℚ) * monomial x.2.1 1
          else 0) := by
  cases o with
  | none => simp
  | some x =>
      simp only [Option.map_some, Option.elim_some]
      split_ifs
      · rw [C_mul_monomial, C_mul_monomial, C_mul_monomial, monomial_mul_monomial]
        simp
      · simp

open Classical in
/-- One step of the product of transition matrices, expanded over strips. -/
theorem mul_walkMatrix_apply (hk : 0 < k) (r : ℕ)
    (A : Matrix (KRestricted N k) (KRestricted N k) (MvPolynomial (Fin N) ℚ))
    (tau lam : KRestricted N k) :
    (A * walkMatrix (N := N) hk r :
        Matrix (KRestricted N k) (KRestricted N k) (MvPolynomial (Fin N) ℚ)) tau lam =
      ∑ δ : Strip N,
      if IsLegal lam.1 δ ∧ stripWeight δ = r then
        A tau (walkTarget hk lam δ) *
          (MvPolynomial.C (walkWeight k lam.1 δ : ℚ) * monomial (walkLabel hk lam δ) 1)
      else 0 := by
  classical
  rw [Matrix.mul_apply]
  simp only [walkMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun δ _ ↦ ?_
  by_cases h : IsLegal lam.1 δ ∧ stripWeight δ = r
  · simp [h]
  · rw [ite_eq_right_iff.mpr fun hh ↦ absurd hh h]
    apply Finset.sum_eq_zero
    intro mu _
    split_ifs with hc
    · exact absurd ⟨hc.1, hc.2.1⟩ h
    · simp

/-- **Entries of the product of walk matrices** as sums over walks.  The `(τ, λ)` entry of the
product of the walk matrices along `l` (first factor applied first) is the sum, over all
sequences of strips of sizes `l` that form a walk from `λ` to `τ`, of the weight times the
monomial of the total label. -/
theorem walkMatrix_prod_apply (hk : 0 < k) (l : List ℕ) (tau lam : KRestricted N k) :
    ((l.map (walkMatrix hk)).reverse.prod) tau lam =
      ∑ ds : Fin l.length → Strip N, (walkFollow hk l ds lam).elim 0
        fun x ↦ if x.1 = tau then MvPolynomial.C (x.2.2 : ℚ) * monomial x.2.1 1 else 0 := by
  classical
  induction l generalizing lam with
  | nil =>
      simp [Matrix.one_apply, walkFollow_nil, eq_comm]
  | cons r l ih =>
      rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton,
        mul_walkMatrix_apply]
      refine Eq.trans ?_ (Fintype.sum_equiv (Fin.consEquiv fun _ ↦ Strip N) _ _
        (fun _ ↦ rfl))
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun δ _ ↦ ?_
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, walkFollow_cons]
      by_cases h : IsLegal lam.1 δ ∧ stripWeight δ = r
      · simp only [h, and_self, ↓reduceIte, elim_map_walk, ← Finset.mul_sum, ← ih]
        ring
      · simp [h]

/-- The coefficient of a monomial in the trace of the product of walk matrices is the total
weight of the closed walks with that label. -/
theorem coeff_trace_walkMatrix_eq_sum (hk : 0 < k) (l : List ℕ) (e : Fin N →₀ ℕ) :
    (Matrix.trace ((l.map (walkMatrix hk)).reverse.prod)).coeff e =
      ∑ lam : KRestricted N k, ∑ ds : Fin l.length → Strip N,
        (walkFollow hk l ds lam).elim 0
          fun x ↦ if x.1 = lam ∧ x.2.1 = e then (x.2.2 : ℚ) else 0 := by
  classical
  rw [Matrix.trace, coeff_sum]
  refine Finset.sum_congr rfl fun lam _ ↦ ?_
  rw [Matrix.diag, walkMatrix_prod_apply, coeff_sum]
  refine Finset.sum_congr rfl fun ds _ ↦ ?_
  cases walkFollow hk l ds lam with
  | none => simp
  | some x =>
      simp only [Option.elim_some]
      by_cases h1 : x.1 = lam
      · by_cases h2 : x.2.1 = e
        · simp [h1, h2, coeff_C_mul, coeff_monomial]
        · simp [h1, h2, coeff_C_mul, coeff_monomial]
      · simp [h1]

/-- **The walk formula.**  Let `0 < k`, `n ≤ N`, `μ ⊢ k n`, and let `l` be any ordering of the
parts of `μ`.  If `R_k(e_μ) = Σ_ν c_ν e_ν` over `ℤ` (the coefficients of the main theorem; they
are unique by `linearIndependent_esymmPart`), then for every `ν ⊢ n`,

  `k ^ N * c_ν = Σ wt(W)`,

the sum over the closed walks `W` on the `k`-restricted vertices whose steps are legal strips of
sizes `l` and whose total label is the multiplicity vector of `ν`. -/
theorem natCast_mul_eq_sum_closedWalks (hk : 0 < k) {n : ℕ} (hn : n ≤ N)
    (mu : (k * n).Partition) (l : List ℕ) (hl : (l : Multiset ℕ) = mu.parts)
    (c : n.Partition → ℕ)
    (hc : exponentDiv k (esymmPart (Fin N) ℤ mu) = ∑ nu, c nu • esymmPart (Fin N) ℤ nu)
    (nu : n.Partition) :
    ((k ^ N * c nu : ℕ) : ℚ) =
      ∑ lam : KRestricted N k, ∑ ds : Fin l.length → Strip N,
        (walkFollow hk l ds lam).elim 0
          fun x ↦ if x.1 = lam ∧ x.2.1 = partitionMultiplicity N nu then (x.2.2 : ℚ) else 0 := by
  rw [← coeff_trace_walkMatrix_eq_sum, coeff_trace_walkMatrix hk hn mu l hl c hc nu]

end PartitionDivision
