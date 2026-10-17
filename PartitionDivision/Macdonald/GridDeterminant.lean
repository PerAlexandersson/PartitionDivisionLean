/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import PartitionDivision.Mathlib.Combinatorics.Enumerative.Partition.Restricted

/-!
# Nonsingularity of partition-grid evaluation matrices

This file proves the algebraic determinant argument which separates lower terms in the
Macdonald evaluation-symmetry induction.  Its two reusable inputs are a strict rearrangement
statement for partition vectors and a generalized Vandermonde determinant whose entries are
powers indexed by dot products.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open Polynomial

namespace Matrix

variable {N : ℕ}

private theorem two_mul_dotProduct_le (a b : Fin N → ℕ) :
    2 * dotProduct a b ≤ dotProduct a a + dotProduct b b := by
  calc
    2 * dotProduct a b = ∑ i, 2 * a i * b i := by
      simp [dotProduct, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ i, ((a i) ^ 2 + (b i) ^ 2) :=
      Finset.sum_le_sum fun i _ ↦ two_mul_le_add_sq (a i) (b i)
    _ = dotProduct a a + dotProduct b b := by
      rw [Finset.sum_add_distrib]
      simp [dotProduct, pow_two]

private theorem two_mul_dotProduct_lt (a b : Fin N → ℕ) (hab : a ≠ b) :
    2 * dotProduct a b < dotProduct a a + dotProduct b b := by
  have hexists : ∃ i, a i ≠ b i := by
    contrapose! hab
    exact funext hab
  calc
    2 * dotProduct a b = ∑ i, 2 * a i * b i := by
      simp [dotProduct, Finset.mul_sum, mul_assoc]
    _ < ∑ i, ((a i) ^ 2 + (b i) ^ 2) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact two_mul_le_add_sq (a i) (b i)
      · obtain ⟨i, hi⟩ := hexists
        refine ⟨i, Finset.mem_univ i, ?_⟩
        have hsquare : (0 : ℤ) < ((a i : ℤ) - b i) ^ 2 :=
          sq_pos_of_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hi))
        exact_mod_cast (show (2 : ℤ) * a i * b i < (a i) ^ 2 + (b i) ^ 2 by
          nlinarith)
    _ = dotProduct a a + dotProduct b b := by
      rw [Finset.sum_add_distrib]
      simp [dotProduct, pow_two]

private theorem permWeight_lt {I : Type*} [Fintype I]
    (v : I → Fin N → ℕ) (hv : Function.Injective v) (σ : Equiv.Perm I) (hσ : σ ≠ 1) :
    (∑ i, dotProduct (v (σ i)) (v i)) < ∑ i, dotProduct (v i) (v i) := by
  have hexists : ∃ i, σ i ≠ i := by
    contrapose! hσ
    exact Equiv.ext hσ
  have hsum :
      (∑ i, 2 * dotProduct (v (σ i)) (v i)) <
        ∑ i, (dotProduct (v (σ i)) (v (σ i)) + dotProduct (v i) (v i)) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact two_mul_dotProduct_le _ _
    · obtain ⟨i, hi⟩ := hexists
      exact ⟨i, Finset.mem_univ i, two_mul_dotProduct_lt _ _ (hv.ne hi)⟩
  have hperm :
      (∑ i, dotProduct (v (σ i)) (v (σ i))) = ∑ i, dotProduct (v i) (v i) := by
    exact Equiv.sum_comp σ (fun i ↦ dotProduct (v i) (v i))
  simp only [Finset.sum_add_distrib, hperm, two_mul] at hsum
  lia

/-- The dot-product power matrix of pairwise distinct natural vectors has nonzero determinant. -/
theorem det_pow_dotProduct_ne_zero {I : Type*} [Fintype I] [DecidableEq I]
    (v : I → Fin N → ℕ) (hv : Function.Injective v) :
    Matrix.det ((fun i j : I ↦
      (Polynomial.X : ℚ[X]) ^ _root_.dotProduct (v i) (v j)) : Matrix I I ℚ[X]) ≠ 0 := by
  let A : Matrix I I ℚ[X] := fun i j ↦
    (Polynomial.X : ℚ[X]) ^ _root_.dotProduct (v i) (v j)
  let D := ∑ i, dotProduct (v i) (v i)
  change A.det ≠ 0
  suffices hcoeff : A.det.coeff D = 1 by
    intro hzero
    rw [hzero, Polynomial.coeff_zero] at hcoeff
    norm_num at hcoeff
  rw [Matrix.det_apply', Polynomial.finsetSum_coeff]
  classical
  rw [Finset.sum_eq_single (1 : Equiv.Perm I)]
  · simp [A, D, Finset.prod_pow_eq_pow_sum]
  · intro σ _ hσ
    have hlt := permWeight_lt v hv σ hσ
    simp only [A, Polynomial.coeff_mul, Finset.prod_pow_eq_pow_sum]
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hab
    rw [Polynomial.coeff_X_pow]
    split_ifs with hb
    · by_cases ha : a = 0
      · subst a
        exfalso
        apply (ne_of_lt hlt)
        have hab' : b = D := by
          simpa using Finset.mem_antidiagonal.mp hab
        simpa [D] using hb.symm.trans hab'
      · simp only [mul_one]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [Polynomial.natDegree_intCast]
        exact Nat.pos_of_ne_zero ha
    · simp
  · simp

end Matrix

namespace Nat.PartitionVector

variable {N : ℕ}

/-- The strictly decreasing staircase vector `(N - 1, N - 2, ..., 0)`. -/
def staircase (N : ℕ) (i : Fin N) : ℕ := N - 1 - i

/-- The staircase vector is strictly decreasing. -/
theorem staircase_strictAnti (N : ℕ) : StrictAnti (staircase N) := by
  intro i j hij
  simp only [staircase]
  have hi := i.isLt
  have hj := j.isLt
  have hij' : (i : ℕ) < j := hij
  lia

/-- The weight of a vector against the staircase `(N - 1, ..., 0)`. -/
def staircaseWeight (v : Fin N → ℕ) : ℕ := dotProduct (staircase N) v

/-- The finset of distinct coordinate rearrangements of a partition vector. -/
def rearrangements (p : PartitionVector N) : Finset (Fin N → ℕ) :=
  Finset.univ.image fun σ : Equiv.Perm (Fin N) ↦ (p : Fin N → ℕ) ∘ σ

/-- Rearranging a partition vector cannot increase its staircase weight. -/
theorem staircaseWeight_comp_perm_le (p : PartitionVector N) (σ : Equiv.Perm (Fin N)) :
    staircaseWeight ((p : Fin N → ℕ) ∘ σ) ≤ staircaseWeight p := by
  have hmonovary : Monovary (staircase N) p :=
    (staircase_strictAnti N).antitone.monovary p.antitone
  simpa [staircaseWeight, dotProduct] using
    hmonovary.sum_mul_comp_perm_le_sum_mul (σ := σ)

/-- Equality in the staircase rearrangement inequality occurs exactly when the rearranged vector
is the original partition vector.  Permutations of equal parts are therefore harmless. -/
theorem staircaseWeight_comp_perm_eq_iff (p : PartitionVector N)
    (σ : Equiv.Perm (Fin N)) :
    staircaseWeight ((p : Fin N → ℕ) ∘ σ) = staircaseWeight p ↔
      (p : Fin N → ℕ) ∘ σ = p := by
  have hmonovary : Monovary (staircase N) p :=
    (staircase_strictAnti N).antitone.monovary p.antitone
  constructor
  · intro h
    have hsorted : Antitone ((p : Fin N → ℕ) ∘ σ) :=
      (staircase_strictAnti N).trans_monovary <|
        (hmonovary.sum_mul_comp_perm_eq_sum_mul_iff (σ := σ)).mp (by
          simpa [staircaseWeight, dotProduct] using h)
          |>.symm
    have heq := Tuple.unique_antitone (f := (p : Fin N → ℕ)) (σ := σ)
      (τ := 1) hsorted (by simpa using p.antitone)
    simpa using heq
  · intro h
    rw [h]

/-- A partition vector itself belongs to its finset of distinct rearrangements. -/
@[simp]
theorem mem_rearrangements_self (p : PartitionVector N) :
    (p : Fin N → ℕ) ∈ p.rearrangements := by
  rw [rearrangements, Finset.mem_image]
  exact ⟨1, Finset.mem_univ _, by simp⟩

/-- Every distinct rearrangement has staircase weight at most that of the partition vector. -/
theorem staircaseWeight_le_of_mem_rearrangements {p : PartitionVector N} {v : Fin N → ℕ}
    (hv : v ∈ p.rearrangements) : staircaseWeight v ≤ staircaseWeight p := by
  rw [rearrangements, Finset.mem_image] at hv
  obtain ⟨σ, _, rfl⟩ := hv
  exact staircaseWeight_comp_perm_le p σ

/-- Among distinct rearrangements, only the partition vector has maximal staircase weight. -/
theorem staircaseWeight_eq_iff_of_mem_rearrangements {p : PartitionVector N}
    {v : Fin N → ℕ} (hv : v ∈ p.rearrangements) :
    staircaseWeight v = staircaseWeight p ↔ v = p := by
  rw [rearrangements, Finset.mem_image] at hv
  obtain ⟨σ, _, rfl⟩ := hv
  exact staircaseWeight_comp_perm_eq_iff p σ

end Nat.PartitionVector

namespace Polynomial

/-- The coefficient at the sum of individual degree bounds of a finite product is the product of
the coefficients at those bounds. -/
theorem coeff_prod_sum_of_natDegree_le {ι R : Type*} [CommSemiring R]
    (s : Finset ι) (f : ι → R[X]) (d : ι → ℕ)
    (hdegree : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hprod : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i := by
        refine (Polynomial.natDegree_prod_le _ _).trans ?_
        exact Finset.sum_le_sum fun i hi ↦ hdegree i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
        Polynomial.coeff_mul_add_eq_of_natDegree_le
          (hdegree a (Finset.mem_insert_self a s)) hprod,
        ih fun i hi ↦ hdegree i (Finset.mem_insert_of_mem hi)]

end Polynomial

namespace Matrix

/-- If the degree bound of a polynomial matrix depends only on the column, then the coefficient
of the determinant at the sum of the bounds is the determinant of the corresponding coefficient
matrix. -/
theorem coeff_det_sum_eq_det_coeff {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (A : Matrix ι ι R[X]) (d : ι → ℕ)
    (hdegree : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.coeff (∑ j, d j) =
      Matrix.det ((fun i j ↦ (A i j).coeff (d j)) : Matrix ι ι R) := by
  let B : Matrix ι ι R := fun i j ↦ (A i j).coeff (d j)
  change A.det.coeff (∑ j, d j) = B.det
  rw [Matrix.det_apply', Polynomial.finsetSum_coeff, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  simp only [B, Polynomial.coeff_intCast_mul]
  rw [Polynomial.coeff_prod_sum_of_natDegree_le]
  exact fun j _ ↦ hdegree (σ j) j

end Matrix

namespace MvPolynomial

/-- The algebra equivalence which views the variables `X 0` and `X 1` as, respectively, the
inner and outer variables of a nested polynomial ring. -/
def finTwoEquivPolynomialPolynomial :
    MvPolynomial (Fin 2) ℚ ≃ₐ[ℚ] ℚ[X][X] :=
  (MvPolynomial.renameEquiv ℚ (Equiv.swap (0 : Fin 2) 1)).trans <|
    (MvPolynomial.finSuccEquiv ℚ 1).trans <|
      Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1))

/-- Under `finTwoEquivPolynomialPolynomial`, `X 0` is the inner variable. -/
@[simp]
theorem finTwoEquivPolynomialPolynomial_X_zero :
    finTwoEquivPolynomialPolynomial (MvPolynomial.X (0 : Fin 2)) =
      Polynomial.C Polynomial.X := by
  simp only [finTwoEquivPolynomialPolynomial, AlgEquiv.trans_apply,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, Equiv.swap_apply_left]
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv ℚ 1 (MvPolynomial.X (Fin.succ (0 : Fin 1)))) =
      Polynomial.C Polynomial.X
  rw [MvPolynomial.finSuccEquiv_X_succ]
  simp [MvPolynomial.uniqueAlgEquiv_apply]

/-- Under `finTwoEquivPolynomialPolynomial`, `X 1` is the outer variable. -/
@[simp]
theorem finTwoEquivPolynomialPolynomial_X_one :
    finTwoEquivPolynomialPolynomial (MvPolynomial.X (1 : Fin 2)) = Polynomial.X := by
  simp only [finTwoEquivPolynomialPolynomial, AlgEquiv.trans_apply,
    MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, Equiv.swap_apply_right]
  rw [MvPolynomial.finSuccEquiv_X_zero]
  simp

/-- The inverse nested-polynomial equivalence sends the inner variable to `X 0`. -/
@[simp]
theorem finTwoEquivPolynomialPolynomial_symm_C_X :
    finTwoEquivPolynomialPolynomial.symm (Polynomial.C Polynomial.X) =
      MvPolynomial.X (0 : Fin 2) := by
  apply finTwoEquivPolynomialPolynomial.injective
  simp

/-- The inverse nested-polynomial equivalence sends the outer variable to `X 1`. -/
@[simp]
theorem finTwoEquivPolynomialPolynomial_symm_X :
    finTwoEquivPolynomialPolynomial.symm Polynomial.X = MvPolynomial.X (1 : Fin 2) := by
  apply finTwoEquivPolynomialPolynomial.injective
  simp

end MvPolynomial

namespace PartitionDivision.Macdonald

open Nat.PartitionVector

variable {N : ℕ}

/-- The orbit sum indexed by a partition vector, evaluated at a point. -/
def orbitSum {R : Type*} [CommSemiring R] (lam : Nat.PartitionVector N)
    (x : Fin N → R) : R :=
  ∑ β ∈ lam.rearrangements, ∏ i, x i ^ β i

/-- The `(q,t)` grid point indexed by a partition vector. -/
def grid {R : Type*} [CommSemiring R] (q t : R) (μ : Nat.PartitionVector N) (i : Fin N) : R :=
  q ^ μ i * t ^ staircase N i

/-- The orbit sum at a grid point, represented with `t` as the outer polynomial variable and
`q` as the inner polynomial variable. -/
def orbitSumGrid (μ lam : Nat.PartitionVector N) : ℚ[X][X] :=
  ∑ β ∈ lam.rearrangements,
    Polynomial.monomial (staircaseWeight β) (Polynomial.X ^ dotProduct μ β)

private theorem prod_grid_eq_monomial (μ : Nat.PartitionVector N) (β : Fin N → ℕ) :
    (∏ i, grid (Polynomial.C (Polynomial.X : ℚ[X])) Polynomial.X μ i ^ β i) =
      Polynomial.monomial (staircaseWeight β) (Polynomial.X ^ dotProduct μ β) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [grid, mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  · simp_rw [← Polynomial.C_pow]
    rw [← map_prod]
    simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, dotProduct]
  · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, staircaseWeight, dotProduct]

/-- The explicit nested-polynomial formula is the orbit sum evaluated at the generic grid. -/
theorem orbitSum_grid_eq_orbitSumGrid (μ lam : Nat.PartitionVector N) :
    orbitSum lam (grid (Polynomial.C (Polynomial.X : ℚ[X])) Polynomial.X μ) =
      orbitSumGrid μ lam := by
  apply Finset.sum_congr rfl
  intro β _
  exact prod_grid_eq_monomial μ β

/-- The `t`-degree of an orbit-sum grid evaluation is bounded by the staircase weight of its
partition index. -/
theorem natDegree_orbitSumGrid_le (μ lam : Nat.PartitionVector N) :
    (orbitSumGrid μ lam).natDegree ≤ staircaseWeight lam := by
  rw [orbitSumGrid]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro β hβ
  exact (Polynomial.natDegree_monomial_le _).trans
    (staircaseWeight_le_of_mem_rearrangements hβ)

/-- The coefficient at maximal `t`-degree in an orbit-sum grid evaluation is
`q ^ dotProduct μ λ`. -/
theorem coeff_orbitSumGrid_staircaseWeight (μ lam : Nat.PartitionVector N) :
    (orbitSumGrid μ lam).coeff (staircaseWeight lam) =
      (Polynomial.X : ℚ[X]) ^ dotProduct μ lam := by
  rw [orbitSumGrid, Polynomial.finsetSum_coeff]
  classical
  rw [Finset.sum_eq_single (lam : Fin N → ℕ)]
  · simp
  · intro β hβ hne
    have hweight : staircaseWeight β ≠ staircaseWeight lam := by
      intro h
      exact hne ((staircaseWeight_eq_iff_of_mem_rearrangements hβ).mp h)
    simp [Polynomial.coeff_monomial, hweight]
  · simp

/-- The polynomial evaluation matrix on any finite set of partition vectors has nonzero
determinant. -/
theorem det_orbitSumGrid_ne_zero (S : Finset (Nat.PartitionVector N)) :
    Matrix.det ((fun μ lam : S ↦ orbitSumGrid μ.1 lam.1) : Matrix S S ℚ[X][X]) ≠ 0 := by
  let A : Matrix S S ℚ[X][X] := fun μ lam ↦ orbitSumGrid μ.1 lam.1
  let d : S → ℕ := fun lam ↦ staircaseWeight lam.1
  let Q : Matrix S S ℚ[X] := fun μ lam ↦
    Polynomial.X ^ dotProduct (μ.1 : Fin N → ℕ) (lam.1 : Fin N → ℕ)
  change A.det ≠ 0
  have hcoeff := Matrix.coeff_det_sum_eq_det_coeff A d fun μ lam ↦
    natDegree_orbitSumGrid_le μ.1 lam.1
  have hcoeff' : A.det.coeff (∑ lam, d lam) = Q.det := by
    calc
      A.det.coeff (∑ lam, d lam) =
          Matrix.det ((fun μ lam ↦ (A μ lam).coeff (d lam)) : Matrix S S ℚ[X]) := hcoeff
      _ = Q.det := congrArg Matrix.det (by
        funext μ lam
        exact coeff_orbitSumGrid_staircaseWeight μ.1 lam.1)
  have hinjective : Function.Injective (fun μ : S ↦ (μ.1 : Fin N → ℕ)) := by
    intro μ ν h
    apply Subtype.ext
    exact Nat.PartitionVector.ext (congrFun h)
  have hq : Q.det ≠ 0 := by
    exact Matrix.det_pow_dotProduct_ne_zero
      (fun μ : S ↦ (μ.1 : Fin N → ℕ)) hinjective
  intro hzero
  apply hq
  rw [← hcoeff', hzero, Polynomial.coeff_zero]

/-- Ring homomorphisms commute with orbit-sum evaluation. -/
theorem map_orbitSum {R K : Type*} [CommSemiring R] [CommSemiring K]
    (φ : R →+* K) (lam : Nat.PartitionVector N) (x : Fin N → R) :
    φ (orbitSum lam x) = orbitSum lam (φ ∘ x) := by
  simp [orbitSum, map_sum, map_prod]

/-- Over any field containing algebraically independent images of the two nested polynomial
variables, every finite orbit-sum grid evaluation matrix is nonsingular. -/
theorem det_orbitSum_grid_ne_zero {K : Type*} [Field K]
    (φ : ℚ[X][X] →+* K) (hφ : Function.Injective φ)
    (S : Finset (Nat.PartitionVector N)) :
    Matrix.det ((fun μ lam : S ↦ orbitSum lam.1
      (grid (φ (Polynomial.C Polynomial.X)) (φ Polynomial.X) μ.1)) : Matrix S S K) ≠ 0 := by
  let A : Matrix S S ℚ[X][X] := fun μ lam ↦ orbitSumGrid μ.1 lam.1
  let B : Matrix S S K := fun μ lam ↦ orbitSum lam.1
    (grid (φ (Polynomial.C Polynomial.X)) (φ Polynomial.X) μ.1)
  change B.det ≠ 0
  have hBA : B = φ.mapMatrix A := by
    funext μ lam
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    change orbitSum lam.1
      (grid (φ (Polynomial.C Polynomial.X)) (φ Polynomial.X) μ.1) =
        φ (orbitSumGrid μ.1 lam.1)
    rw [← orbitSum_grid_eq_orbitSumGrid]
    rw [map_orbitSum]
    congr 2
    funext i
    simp [grid]
  rw [hBA, ← φ.map_det]
  exact (map_ne_zero_iff φ hφ).mpr (det_orbitSumGrid_ne_zero S)

/-- An injective image of the bivariate polynomial ring supplies algebraically independent grid
parameters, so the corresponding evaluation matrix is nonsingular. -/
theorem det_orbitSum_grid_ne_zero_of_mvPolynomial {K : Type*} [Field K]
    (φ : MvPolynomial (Fin 2) ℚ →+* K) (hφ : Function.Injective φ)
    (S : Finset (Nat.PartitionVector N)) :
    Matrix.det ((fun μ lam : S ↦ orbitSum lam.1
      (grid (φ (MvPolynomial.X 0)) (φ (MvPolynomial.X 1)) μ.1)) : Matrix S S K) ≠ 0 := by
  let ψ : ℚ[X][X] →+* K :=
    φ.comp MvPolynomial.finTwoEquivPolynomialPolynomial.symm.toRingHom
  have hψ : Function.Injective ψ :=
    hφ.comp MvPolynomial.finTwoEquivPolynomialPolynomial.symm.injective
  simpa [ψ] using det_orbitSum_grid_ne_zero ψ hψ S

/-- For `q = X 0` and `t = X 1` in the fraction field of the bivariate polynomial ring, every
finite orbit-sum grid evaluation matrix is nonsingular. -/
theorem det_orbitSum_grid_fractionRing_ne_zero
    (S : Finset (Nat.PartitionVector N)) :
    Matrix.det ((fun μ lam : S ↦ orbitSum lam.1 (grid
      (algebraMap (MvPolynomial (Fin 2) ℚ)
        (FractionRing (MvPolynomial (Fin 2) ℚ)) (MvPolynomial.X 0))
      (algebraMap (MvPolynomial (Fin 2) ℚ)
        (FractionRing (MvPolynomial (Fin 2) ℚ)) (MvPolynomial.X 1)) μ.1)) :
          Matrix S S (FractionRing (MvPolynomial (Fin 2) ℚ))) ≠ 0 := by
  exact det_orbitSum_grid_ne_zero_of_mvPolynomial
    (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ)))
    (IsFractionRing.injective (MvPolynomial (Fin 2) ℚ)
      (FractionRing (MvPolynomial (Fin 2) ℚ))) S

end PartitionDivision.Macdonald

