/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import PartitionDivision.Mathlib.Combinatorics.Enumerative.ContingencyTable
public import PartitionDivision.Mathlib.Algebra.MvPolynomial.CoeffProd
public import PartitionDivision.TauCeti.RingTheory.MvPolynomial.Symmetric.Complete
public import PartitionDivision.TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Monomial

/-!
# The `(q, t)`-analogues `g_n` of the complete homogeneous symmetric polynomials

Following Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter VI, (2.8), let

`gₙ(x; q, t) = ∑_{|α| = n} (∏ᵢ c(αᵢ)) x^α`, where
`c(m) = (t; q)_m / (q; q)_m = ∏_{i<m} (1 - t qⁱ)/(1 - q^{i+1})`,

so that `∑ₙ gₙ uⁿ = ∏ᵢ f(xᵢ u)` with `f(z) = ∑ₘ c(m) zᵐ`; analytically `f(z) = (tz; q)_∞/(z; q)_∞`.
For a partition `μ` put `g_μ = ∏ g_{μᵢ}`.  At `q = t = 0` every `c(m)` is `1` and `g_μ = h_μ`.

## Division-free coefficients

The coefficient `c(m)` is defined over an arbitrary commutative ring, as
`MvPolynomial.macdonaldGCoeff q t m = ∏_{i<m} (1 - t qⁱ) * Ring.inverse (1 - q^{i+1})`.  Over a
field this is the quotient above (`MvPolynomial.macdonaldGCoeff_eq_prod_div`), and no
hypothesis is needed for the definition.  When the denominators `1 - q^{i+1}` are units, i.e. when
`q` is not a root of unity in a field, the coefficients commute with ring homomorphisms
(`MvPolynomial.map_macdonaldGCoeff`) and satisfy the `q`-difference equation
`(1 - q^{m+1}) c(m+1) = (1 - t q^m) c(m)` that characterizes `f`
(`MvPolynomial.one_sub_pow_mul_macdonaldGCoeff_succ`).  Working over a ring rather than a field is
what allows the specialization `q = t = 0` to be a ring homomorphism, which the basis theorem in
`PartitionDivision/Macdonald/GBasis.lean` uses.

## The transition matrix

The coefficient of `x^c` in `∏ᵢ g_{rᵢ}` is the sum over the contingency tables `A` with row sums
`r` and column sums `c` of `∏_{i,j} c(A_{ij})` (`MvPolynomial.coeff_prod_macdonaldG`).  This is the
coefficient of `x^c y^r` in the kernel `∏_{i,j} f(xᵢ yⱼ)`, and it is visibly symmetric under
transposing the table (`MvPolynomial.macdonaldKernelCoeff_comm`).  Consequently the matrix
`G_{μν} = [x^ν] g_μ` is symmetric (`MvPolynomial.coeff_macdonaldGPart_partWeight_comm`), which is
Macdonald VI (2.19)--(2.20) in finitely many variables, proved without power series.

## Main definitions

* `MvPolynomial.macdonaldGCoeff q t m`: the coefficient `(t; q)_m / (q; q)_m`.
* `MvPolynomial.macdonaldG σ q t n`: the polynomial `gₙ` in the variables `σ`.
* `MvPolynomial.macdonaldGPart σ q t μ`: the product `g_μ` over the parts of a partition.
* `MvPolynomial.macdonaldKernelCoeff q t r c`: the coefficient of `x^c y^r` in `∏_{i,j} f(xᵢ yⱼ)`,
  as a sum over contingency tables.

## Main results

* `MvPolynomial.coeff_macdonaldG`, `MvPolynomial.mk_macdonaldG_eq_prod`: the coefficients and the
  generating function of the `gₙ`.
* `MvPolynomial.macdonaldG_isSymmetric`, `MvPolynomial.isHomogeneous_macdonaldG` and the
  corresponding statements for `g_μ`.
* `MvPolynomial.macdonaldG_zero_zero`, `MvPolynomial.macdonaldGPart_zero_zero`: at `q = t = 0`,
  `gₙ = hₙ` and `g_μ = h_μ`.
* `MvPolynomial.map_macdonaldG`, `MvPolynomial.map_macdonaldGPart`: compatibility with ring
  homomorphisms when the denominators are units.
* `MvPolynomial.coeff_macdonaldGPart_partWeight` and
  `MvPolynomial.coeff_macdonaldGPart_partWeight_comm`: the matrix `[x^ν] g_μ` is the kernel
  coefficient, hence symmetric in `μ` and `ν`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter VI,
  (2.8) and (2.19)--(2.21).
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### The one-variable coefficients -/

/-- **The coefficient `(t; q)ₙ / (q; q)ₙ`** of `zⁿ` in `(tz; q)_∞ / (z; q)_∞`, written as
`∏_{i<n} (1 - t qⁱ) (1 - q^{i+1})⁻¹`.  The inverse is `Ring.inverse`, so the definition makes sense
in every commutative ring; it is the honest quotient when the denominators are units
(`MvPolynomial.macdonaldGCoeff_eq_prod_div` over a field). -/
noncomputable def macdonaldGCoeff (q t : R) (n : ℕ) : R :=
  ∏ i ∈ range n, (1 - t * q ^ i) * Ring.inverse (1 - q ^ (i + 1))

/-- The constant coefficient of `(tz; q)_∞ / (z; q)_∞` is `1`. -/
@[simp]
theorem macdonaldGCoeff_zero (q t : R) : macdonaldGCoeff q t 0 = 1 := by
  simp [macdonaldGCoeff]

/-- The recursion defining `(t; q)ₙ / (q; q)ₙ` as a product. -/
theorem macdonaldGCoeff_succ (q t : R) (n : ℕ) :
    macdonaldGCoeff q t (n + 1) =
      macdonaldGCoeff q t n * ((1 - t * q ^ n) * Ring.inverse (1 - q ^ (n + 1))) :=
  prod_range_succ _ _

/-- **At `q = t = 0` every coefficient is `1`**, so the series `(tz; q)_∞ / (z; q)_∞` becomes the
geometric series `1 / (1 - z)`. -/
@[simp]
theorem macdonaldGCoeff_zero_zero (n : ℕ) : macdonaldGCoeff (0 : R) 0 n = 1 := by
  simp [macdonaldGCoeff]

/-- Over a field the coefficient is the quotient `∏_{i<n} (1 - t qⁱ) / (1 - q^{i+1})`. -/
theorem macdonaldGCoeff_eq_prod_div {K : Type*} [Field K] (q t : K) (n : ℕ) :
    macdonaldGCoeff q t n = ∏ i ∈ range n, (1 - t * q ^ i) / (1 - q ^ (i + 1)) := by
  simp [macdonaldGCoeff, Ring.inverse_eq_inv', div_eq_mul_inv]

/-- **The `q`-difference equation** `(1 - q^{n+1}) c(n+1) = (1 - t qⁿ) c(n)`, which together with
`c(0) = 1` determines the coefficients of `(tz; q)_∞ / (z; q)_∞`, valid when the denominators
`1 - q^{i+1}` are units. -/
theorem one_sub_pow_mul_macdonaldGCoeff_succ {q : R} (hq : ∀ i, IsUnit (1 - q ^ (i + 1)))
    (t : R) (n : ℕ) :
    (1 - q ^ (n + 1)) * macdonaldGCoeff q t (n + 1) = (1 - t * q ^ n) * macdonaldGCoeff q t n := by
  rw [macdonaldGCoeff_succ, mul_left_comm, ← mul_assoc (1 - q ^ (n + 1)),
    mul_comm _ (1 - t * q ^ n)]
  rw [mul_assoc, Ring.mul_inverse_cancel _ (hq n), mul_one, mul_comm]

/-- **The coefficients commute with ring homomorphisms** once the denominators `1 - q^{i+1}` are
units, since a ring homomorphism maps the inverse of a unit to the inverse of its image. -/
theorem map_macdonaldGCoeff (f : R →+* S) {q : R} (hq : ∀ i, IsUnit (1 - q ^ (i + 1)))
    (t : R) (n : ℕ) : f (macdonaldGCoeff q t n) = macdonaldGCoeff (f q) (f t) n := by
  simp only [macdonaldGCoeff, map_prod, map_mul, map_sub, map_one, map_pow]
  refine prod_congr rfl fun i _ ↦ ?_
  obtain ⟨u, hu⟩ := hq i
  have hu' : (Units.map f.toMonoidHom u : S) = 1 - f q ^ (i + 1) := by
    simp [hu]
  rw [← hu, ← hu', Ring.inverse_unit, Ring.inverse_unit]
  simp

/-! ### The polynomials `gₙ` and `g_μ` -/

variable (σ : Type*) [Fintype σ] [DecidableEq σ]

/-- **The polynomial `gₙ(x; q, t)`** of Macdonald VI (2.8) in the variables `σ`: the sum over the
exponents `α` of total degree `n` of `(∏ᵢ c(αᵢ)) x^α`, where `c = MvPolynomial.macdonaldGCoeff q t`.
It is the coefficient of `uⁿ` in `∏ᵢ f(xᵢ u)` with `f(z) = ∑ₘ c(m) zᵐ`
(`MvPolynomial.mk_macdonaldG_eq_prod`). -/
noncomputable def macdonaldG (q t : R) (n : ℕ) : MvPolynomial σ R :=
  ∑ α ∈ (univ : Finset σ).finsuppAntidiag n, monomial α (∏ i, macdonaldGCoeff q t (α i))

/-- **The polynomial `g_μ = ∏ᵢ g_{μᵢ}`** of a partition `μ`, the product of
`MvPolynomial.macdonaldG` over the parts, in the convention of `MvPolynomial.hsymmPart`. -/
noncomputable def macdonaldGPart (q t : R) {n : ℕ} (μ : n.Partition) : MvPolynomial σ R :=
  (μ.parts.map (macdonaldG σ q t)).prod

variable {σ}

/-- **The coefficients of `gₙ`**: the coefficient at `x^β` is `∏ᵢ c(βᵢ)` if `β` has total degree
`n`, and `0` otherwise. -/
theorem coeff_macdonaldG (q t : R) (n : ℕ) (β : σ →₀ ℕ) :
    (macdonaldG σ q t n).coeff β =
      if β.degree = n then ∏ i, macdonaldGCoeff q t (β i) else 0 := by
  rw [macdonaldG, coeff_sum]
  simp only [coeff_monomial]
  rw [sum_ite_eq']
  simp [Finsupp.degree_eq_sum]

/-- `g₀ = 1`. -/
@[simp]
theorem macdonaldG_zero (q t : R) : macdonaldG σ q t 0 = 1 := by
  simp [macdonaldG]

/-- **The generating function of the `gₙ`**: `∑ₙ gₙ uⁿ = ∏ᵢ ∑ₘ c(m) xᵢᵐ uᵐ`, as power series in
`u` over `MvPolynomial σ R`.  Each factor is `f(xᵢ u)` with `f(z) = ∑ₘ c(m) zᵐ`, the series of
`(tz; q)_∞ / (z; q)_∞`. -/
theorem mk_macdonaldG_eq_prod (q t : R) :
    PowerSeries.mk (fun n ↦ macdonaldG σ q t n) =
      ∏ i, PowerSeries.mk fun n ↦ C (macdonaldGCoeff q t n) * (X i : MvPolynomial σ R) ^ n := by
  refine PowerSeries.ext fun d ↦ ?_
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_prod, macdonaldG]
  refine sum_congr rfl fun α _ ↦ ?_
  simp only [PowerSeries.coeff_mk]
  rw [prod_mul_distrib, ← map_prod, monomial_eq,
    Finsupp.prod_fintype α (fun i e ↦ (X i : MvPolynomial σ R) ^ e) fun _ ↦ pow_zero _]

/-- `gₙ` is homogeneous of degree `n`. -/
theorem isHomogeneous_macdonaldG (q t : R) (n : ℕ) : (macdonaldG σ q t n).IsHomogeneous n :=
  IsHomogeneous.sum _ _ _ fun α hα ↦ isHomogeneous_monomial _ <| by
    simpa [Finsupp.degree_eq_sum] using hα

/-- `gₙ` is symmetric: its coefficient at `x^β` depends only on the multiset of exponents. -/
theorem macdonaldG_isSymmetric (q t : R) (n : ℕ) : (macdonaldG σ q t n).IsSymmetric := by
  intro e
  ext β
  obtain ⟨γ, rfl⟩ : ∃ γ, Finsupp.mapDomain e γ = β := ⟨Finsupp.mapDomain e.symm β, by
    rw [← Finsupp.mapDomain_comp]; simp⟩
  have happ (i : σ) : Finsupp.mapDomain e γ (e i) = γ i :=
    Finsupp.mapDomain_apply_of_injective e.injective γ i
  have hdeg : (Finsupp.mapDomain e γ).degree = γ.degree := by
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, ← Equiv.sum_comp e]
    simp only [happ]
  have hprod : ∏ i, macdonaldGCoeff q t (Finsupp.mapDomain e γ i) =
      ∏ i, macdonaldGCoeff q t (γ i) := by
    rw [← Equiv.prod_comp e]
    simp only [happ]
  rw [coeff_rename_mapDomain _ e.injective, coeff_macdonaldG, coeff_macdonaldG, hdeg, hprod]

/-- **`gₙ` commutes with ring homomorphisms** once the denominators `1 - q^{i+1}` are units. -/
theorem map_macdonaldG (f : R →+* S) {q : R} (hq : ∀ i, IsUnit (1 - q ^ (i + 1))) (t : R)
    (n : ℕ) : map f (macdonaldG σ q t n) = macdonaldG σ (f q) (f t) n := by
  simp [macdonaldG, map_macdonaldGCoeff f hq]

/-- **At `q = t = 0`, `gₙ` is the complete homogeneous symmetric polynomial `hₙ`.** -/
theorem macdonaldG_zero_zero (n : ℕ) : macdonaldG σ (0 : R) 0 n = hsymm σ R n := by
  rw [TauCeti.hsymm_eq_sum_piAntidiag, macdonaldG, finsuppAntidiag, sum_map,
    ← sum_attach (piAntidiag univ n)]
  refine sum_congr rfl fun γ _ ↦ ?_
  rw [prod_X_pow]
  simp only [macdonaldGCoeff_zero_zero, prod_const_one]
  exact congrArg (fun d ↦ monomial d (1 : R)) (Finsupp.ext fun i ↦ by simp)

/-- **`g_μ` commutes with ring homomorphisms** once the denominators `1 - q^{i+1}` are units. -/
theorem map_macdonaldGPart (f : R →+* S) {q : R} (hq : ∀ i, IsUnit (1 - q ^ (i + 1))) (t : R)
    {n : ℕ} (μ : n.Partition) :
    map f (macdonaldGPart σ q t μ) = macdonaldGPart σ (f q) (f t) μ := by
  simp [macdonaldGPart, map_multiset_prod, Multiset.map_map, map_macdonaldG f hq]

/-- **At `q = t = 0`, `g_μ` is the complete homogeneous symmetric polynomial `h_μ`.** -/
theorem macdonaldGPart_zero_zero {n : ℕ} (μ : n.Partition) :
    macdonaldGPart σ (0 : R) 0 μ = hsymmPart σ R μ := by
  simp [macdonaldGPart, hsymmPart, macdonaldG_zero_zero]

/-- `g_μ` is homogeneous of degree `|μ|`. -/
theorem isHomogeneous_macdonaldGPart (q t : R) {n : ℕ} (μ : n.Partition) :
    (macdonaldGPart σ q t μ).IsHomogeneous n := by
  have key (s : Multiset ℕ) : ((s.map (macdonaldG σ q t)).prod).IsHomogeneous s.sum := by
    induction s using Multiset.induction_on with
    | empty => simpa using isHomogeneous_one σ R
    | cons a s ih =>
      simpa using (isHomogeneous_macdonaldG q t a).mul ih
  simpa [macdonaldGPart, μ.parts_sum] using key μ.parts

/-- `g_μ` is symmetric, being a product of symmetric polynomials. -/
theorem macdonaldGPart_isSymmetric (q t : R) {n : ℕ} (μ : n.Partition) :
    (macdonaldGPart σ q t μ).IsSymmetric := by
  rw [← mem_symmetricSubalgebra]
  exact Subalgebra.multiset_prod_mem _ fun p hp ↦ by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hp
    exact macdonaldG_isSymmetric q t a

/-! ### The kernel coefficients and the transition matrix -/

section Kernel

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **The coefficient of `x^c y^r` in the kernel `∏_{i,j} f(xᵢ yⱼ)`**, with
`f(z) = ∑ₘ c(m) zᵐ`: the sum over the contingency tables `A` with row sums `r` and column sums `c`
of `∏_{i,j} c(A_{ij})`.  By `MvPolynomial.coeff_prod_macdonaldG` it is the coefficient of `x^c` in
`∏ᵢ g_{rᵢ}`. -/
noncomputable def macdonaldKernelCoeff (q t : R) (r : ι → ℕ) (c : κ → ℕ) : R :=
  ∑ A ∈ contingencyTables r c, ∏ i, ∏ j, macdonaldGCoeff q t (A i j)

/-- **The kernel coefficients are symmetric**: transposing the contingency tables exchanges the
roles of the row and column sums. -/
theorem macdonaldKernelCoeff_comm (q t : R) (r : ι → ℕ) (c : κ → ℕ) :
    macdonaldKernelCoeff q t r c = macdonaldKernelCoeff q t c r := by
  rw [macdonaldKernelCoeff, sum_contingencyTables_comm, macdonaldKernelCoeff]
  exact sum_congr rfl fun A _ ↦ prod_comm

/-- **The coefficients of a product of `g`'s**: the coefficient of `x^c` in `∏ᵢ g_{rᵢ}` is the
kernel coefficient, the sum over the contingency tables with row sums `r` and column sums `c` of
`∏_{i,j} c(A_{ij})`.  Row `i` of a table is the exponent taken from the factor `g_{rᵢ}`. -/
theorem coeff_prod_macdonaldG (q t : R) (r : ι → ℕ) (c : σ →₀ ℕ) :
    (∏ i, macdonaldG σ q t (r i)).coeff c = macdonaldKernelCoeff q t r c := by
  have hterm (l : ι →₀ σ →₀ ℕ) : ∏ i, (macdonaldG σ q t (r i)).coeff (l i) =
      if ∀ i, (l i).degree = r i then ∏ i, ∏ j, macdonaldGCoeff q t (l i j) else 0 := by
    simp_rw [coeff_macdonaldG]
    exact Fintype.prod_ite_zero
  rw [coeff_prod, macdonaldKernelCoeff]
  simp_rw [hterm]
  rw [← sum_filter]
  refine sum_nbij' (fun l i j ↦ l i j)
    (fun A ↦ Finsupp.equivFunOnFinite.symm fun i ↦ Finsupp.equivFunOnFinite.symm (A i))
    (fun l hl ↦ ?_) (fun A hA ↦ ?_) (fun l _ ↦ ?_) (fun A _ ↦ rfl) fun l _ ↦ rfl
  · simp only [mem_filter, mem_finsuppAntidiag, subset_univ, and_true] at hl
    simp only [mem_contingencyTables]
    refine ⟨fun i ↦ by rw [← hl.2 i, Finsupp.degree_eq_sum], fun j ↦ ?_⟩
    rw [← hl.1, Finsupp.finsetSum_apply]
  · simp only [mem_contingencyTables] at hA
    simp only [mem_filter, mem_finsuppAntidiag, subset_univ, and_true]
    refine ⟨Finsupp.ext fun j ↦ ?_, fun i ↦ ?_⟩
    · rw [Finsupp.finsetSum_apply]
      simpa using hA.2 j
    · simpa [Finsupp.degree_eq_sum] using hA.1 i
  · ext i j
    simp

/-- **`g_μ` as a product over the alphabet**: for a partition `μ` with at most `|σ|` parts,
`g_μ = ∏_{x ∈ σ} g_{μ(x)}`, where `μ(x)` is the part of `μ` recorded at `x` by
`TauCeti.partWeight` (zero beyond the length of `μ`, and `g₀ = 1`). -/
theorem macdonaldGPart_eq_prod_partWeight (q t : R) {n : ℕ} (μ : n.Partition)
    (hμ : μ.parts.card ≤ Fintype.card σ) :
    macdonaldGPart σ q t μ = ∏ x, macdonaldG σ q t (TauCeti.partWeight σ μ x) := by
  have h := congrArg Nat.Partition.parts
    (TauCeti.weightPartition_partWeight μ hμ (TauCeti.degree_partWeight μ hμ))
  rw [TauCeti.weightPartition_parts] at h
  rw [macdonaldGPart, ← h, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  refine prod_subset (subset_univ _) fun x _ hx ↦ ?_
  rw [Function.comp_apply, Finsupp.notMem_support_iff.mp hx, macdonaldG_zero]

/-- **The transition matrix from `g` to the monomial symmetric polynomials is a kernel
coefficient**: for partitions `μ, ν` of `n`, `μ` with at most `|σ|` parts, the coefficient of the
sorted monomial `x^ν` in `g_μ` is the coefficient of `x^ν y^μ` in `∏_{i,j} f(xᵢ yⱼ)`. -/
theorem coeff_macdonaldGPart_partWeight (q t : R) {n : ℕ} (μ ν : n.Partition)
    (hμ : μ.parts.card ≤ Fintype.card σ) :
    (macdonaldGPart σ q t μ).coeff (TauCeti.partWeight σ ν) =
      macdonaldKernelCoeff q t (TauCeti.partWeight σ μ) (TauCeti.partWeight σ ν) := by
  rw [macdonaldGPart_eq_prod_partWeight q t μ hμ, coeff_prod_macdonaldG]

/-- **The transition matrix `G_{μν} = [x^ν] g_μ` is symmetric** (Macdonald VI (2.19)--(2.20) in
finitely many variables): for partitions `μ, ν` of `n` with at most `|σ|` parts, the coefficient
of `x^ν` in `g_μ` equals the coefficient of `x^μ` in `g_ν`. -/
theorem coeff_macdonaldGPart_partWeight_comm (q t : R) {n : ℕ} (μ ν : n.Partition)
    (hμ : μ.parts.card ≤ Fintype.card σ) (hν : ν.parts.card ≤ Fintype.card σ) :
    (macdonaldGPart σ q t μ).coeff (TauCeti.partWeight σ ν) =
      (macdonaldGPart σ q t ν).coeff (TauCeti.partWeight σ μ) := by
  rw [coeff_macdonaldGPart_partWeight q t μ ν hμ, coeff_macdonaldGPart_partWeight q t ν μ hν,
    macdonaldKernelCoeff_comm]

end Kernel

end MvPolynomial
