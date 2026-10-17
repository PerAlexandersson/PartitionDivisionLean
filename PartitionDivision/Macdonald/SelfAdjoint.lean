/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import PartitionDivision.Macdonald.Kernel
public import PartitionDivision.Macdonald.KernelIdentity
public import PartitionDivision.Macdonald.Operator
public import PartitionDivision.Macdonald.GridEvaluation

/-!
# Self-adjointness of the Macdonald operators (Pieri ledger Lemma 5)

Let `K` be a field of characteristic zero, `q, t ∈ K` with every `1 - q^{k+1}` a unit, and suppose
the `g_λ` form a basis of the degree-`d` symmetric polynomials in `N` variables (the determinant
hypothesis of `MvPolynomial.macdonaldPairing`).  Then every Macdonald operator `D_N^r`, restricted
to the symmetric polynomials of degree `d` (`MvPolynomial.macdonaldOpHom`), is self-adjoint for the
`(q, t)` pairing (`MvPolynomial.isSelfAdjoint_macdonaldOpHom`).  This holds in particular over
`ℚ(q, t)` (`MvPolynomial.isSelfAdjoint_macdonaldOpHom_fractionRing`) and over every field receiving
an injective ring homomorphism from `ℚ[q, t]`
(`MvPolynomial.isSelfAdjoint_macdonaldOpHom_of_injective`).  This is Macdonald VI (3.11)--(3.12).

## The argument

By the criterion `MvPolynomial.isSelfAdjoint_macdonaldPairing_iff` it suffices to show that
`D` acting in `x` and in `y` agree on the kernel `Π_d = ∑_λ g_λ(x) m_λ(y)`.  We work in
`A = K[x, y]` (variables `Fin N ⊕ Fin N`) and in the power series ring `A[[u]]`, where `u` records
the degree.

1. `Π(u) = ∏_{i,j} f(xᵢ yⱼ u)` has `u^d`-coefficient `Π_d` (`MvPolynomial.coeff_macdonaldKernelU`).
   The `q`-shift `T_{q,I}` in the `x` (or `y`) variables satisfies
   `T_{q,I} Π · ∏_{i∈I,j} (1 - t xᵢ yⱼ u) = Π · ∏_{i∈I,j} (1 - xᵢ yⱼ u)`
   (`MvPolynomial.map_macdonaldKernelU_mul_left`, `MvPolynomial.map_macdonaldKernelU_mul_right`).
2. The defining identity `V · D f = ∑_{|I| = r} T_{t,I} V · T_{q,I} f` of the operators, applied to
   each `g_λ` (resp. `m_λ`), gives `V(x) · D_x Π = ∑_I T_{t,I} V(x) · T^x_{q,I} Π`
   (`MvPolynomial.C_vandermonde_mul_macdonaldOpLeftU`), and the same in `y`.
3. Multiplying by `W = ∏_{i,j} (1 - t xᵢ yⱼ u)` and using step 1, `V(x) · W · D_x Π = Π · Q_x` and
   `V(y) · W · D_y Π = Π · Q_y` with explicit polynomials `Q_x, Q_y` in `u`.
4. `V(y) · Q_x = V(x) · Q_y` (`MvPolynomial.C_vandermonde_mul_macdonaldKernelSumLeft`): in the
   fraction field of `A[[u]]`, after dividing by `V(x) V(y) t^{r(r-1)/2} W`, the two sides are
   `kernelSum(x, uy)` and `kernelSum(uy, x)`, using the Vandermonde ratio
   `Nat.PartitionVector.Macdonald.eval_scaleSubset_vandermonde`; they agree by
   `Macdonald.kernelSum_comm`.
5. `A[[u]]` is a domain, so cancelling `V(x) V(y) W` gives `D_x Π = D_y Π`, hence
   `D_x Π_d = D_y Π_d` for every `d` (`MvPolynomial.macdonaldOpLeft_eq_macdonaldOpRight`).

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter VI,
  (3.11)--(3.12).
-/

@[expose] public section

open Finset TauCeti

namespace MvPolynomial

section Coeff

variable {σ τ R : Type*} [CommSemiring R]

/-- Embedding two exponent vectors into a disjoint sum of alphabets and adding them gives
`Finsupp.sumElim`. -/
theorem mapDomain_inl_add_mapDomain_inr (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    Finsupp.mapDomain Sum.inl a + Finsupp.mapDomain Sum.inr b = Finsupp.sumElim a b := by
  ext (x | x) <;>
    simp [Finsupp.mapDomain_apply_of_injective Sum.inl_injective,
      Finsupp.mapDomain_apply_of_injective Sum.inr_injective, Finsupp.mapDomain_of_notMem_range]

/-- `Finsupp.sumElim` is injective. -/
theorem sumElim_eq_sumElim_iff {a a' : σ →₀ ℕ} {b b' : τ →₀ ℕ} :
    Finsupp.sumElim a b = Finsupp.sumElim a' b' ↔ a = a' ∧ b = b' := by
  refine ⟨fun h ↦ ⟨Finsupp.ext fun x ↦ ?_, Finsupp.ext fun x ↦ ?_⟩, fun h ↦ by rw [h.1, h.2]⟩
  · simpa using congrArg (· (Sum.inl x)) h
  · simpa using congrArg (· (Sum.inr x)) h

/-- The coefficient of `x^r y^c` in `p(x) m(y)` is the product of the coefficients. -/
theorem coeff_sumElim_rename_mul_rename (p : MvPolynomial σ R) (m : MvPolynomial τ R)
    (r : σ →₀ ℕ) (c : τ →₀ ℕ) :
    (rename Sum.inl p * rename Sum.inr m).coeff (Finsupp.sumElim r c) = p.coeff r * m.coeff c := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a k =>
    induction m using MvPolynomial.induction_on' with
    | monomial b l =>
      rw [rename_monomial, rename_monomial, monomial_mul_monomial, coeff_monomial, coeff_monomial,
        coeff_monomial, mapDomain_inl_add_mapDomain_inr]
      by_cases ha : a = r <;> by_cases hb : b = c <;> simp [ha, hb, sumElim_eq_sumElim_iff]
    | add m₁ m₂ h₁ h₂ => simp [mul_add, h₁, h₂]
  | add p₁ p₂ h₁ h₂ => simp [add_mul, h₁, h₂]

/-- A finite product of monomials is a monomial. -/
theorem prod_monomial {ι : Type*} (s : Finset ι) (e : ι → σ →₀ ℕ) (a : ι → R) :
    ∏ i ∈ s, monomial (e i) (a i) = monomial (∑ i ∈ s, e i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [prod_insert hx, ih, monomial_mul_monomial, sum_insert hx, prod_insert hx]

end Coeff

section Scale

variable {τ K : Type*} [CommSemiring K]

/-- Rescale every variable: `X s ↦ v s • X s`. -/
noncomputable def scaleVarsBy (v : τ → K) : MvPolynomial τ K →ₐ[K] MvPolynomial τ K :=
  aeval fun s ↦ v s • X s

/-- Rescaling the variables multiplies the monomial `x^e` by `∏ v_s^{e_s}`. -/
theorem scaleVarsBy_monomial (v : τ → K) (e : τ →₀ ℕ) (a : K) :
    scaleVarsBy v (monomial e a) = monomial e (a * e.prod fun s k ↦ v s ^ k) := by
  rw [scaleVarsBy, aeval_monomial, monomial_eq]
  simp only [Finsupp.prod, smul_eq_C_mul, mul_pow, algebraMap_eq, C_mul, map_prod, map_pow,
    prod_mul_distrib]
  ring

end Scale

section Series

variable {K : Type*} [Field K] {N : ℕ}

/-- **The degree-`d` kernel in `2N` variables**: `Π_d = ∑_λ g_λ(x) m_λ(y)`, with
`xᵢ = X (inl i)` and `yⱼ = X (inr j)`, summed over the partitions `λ` of `d` with at most `N`
parts. -/
noncomputable def macdonaldKernelPoly (q t : K) (d : ℕ) : MvPolynomial (Fin N ⊕ Fin N) K :=
  ∑ ν : {ν : d.Partition // ν.parts.card ≤ Fintype.card (Fin N)},
    rename Sum.inl (macdonaldGPart (Fin N) q t ν.1) * rename Sum.inr (msymm (Fin N) K ν.1)

/-- The coefficient of `x^r y^c` in `Π_d` is the kernel coefficient when `|r| = |c| = d`. -/
theorem coeff_macdonaldKernelPoly (q t : K) (d : ℕ) (r c : Fin N →₀ ℕ) :
    (macdonaldKernelPoly q t d).coeff (Finsupp.sumElim r c) =
      if r.degree = d ∧ c.degree = d then macdonaldKernelCoeff q t ⇑r ⇑c else 0 := by
  rw [← coeff_coeff_macdonaldKernel, macdonaldKernel_eq_sum, macdonaldKernelPoly]
  simp only [coeff_sum]
  refine sum_congr rfl fun ν _ ↦ ?_
  rw [coeff_sumElim_rename_mul_rename, mul_comm (map C _), coeff_C_mul, coeff_map,
    mul_comm (msymm (Fin N) K _), coeff_C_mul]

/-- The factor `f(xᵢ yⱼ u) = ∑ₙ c(n) (xᵢ yⱼ)ⁿ uⁿ` of the kernel, as a power series in `u` over
`K[x, y]`. -/
noncomputable def macdonaldKernelFactorU (q t : K) (i j : Fin N) :
    PowerSeries (MvPolynomial (Fin N ⊕ Fin N) K) :=
  PowerSeries.mk fun n ↦ monomial (n • macdonaldKernelExponent (Fin N) i j) (macdonaldGCoeff q t n)

/-- **The kernel `Π(u) = ∏_{i,j} f(xᵢ yⱼ u)`**, as a power series in `u` over `K[x, y]`. -/
noncomputable def macdonaldKernelU (q t : K) : PowerSeries (MvPolynomial (Fin N ⊕ Fin N) K) :=
  ∏ i, ∏ j, macdonaldKernelFactorU q t i j

/-- **The `u^d`-coefficient of `∏_{i,j} f(xᵢ yⱼ u)` is `Π_d = ∑_λ g_λ(x) m_λ(y)`.** -/
theorem coeff_macdonaldKernelU (q t : K) (d : ℕ) :
    PowerSeries.coeff d (macdonaldKernelU (N := N) q t) = macdonaldKernelPoly q t d := by
  classical
  ext e
  obtain ⟨⟨r, c⟩, rfl⟩ := Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective e
  have he : Finsupp.sumFinsuppEquivProdFinsupp.symm (r, c) = Finsupp.sumElim r c := by
    ext (x | x) <;> simp
  rw [he, coeff_macdonaldKernelPoly, macdonaldKernelU, ← Fintype.prod_prod_type',
    PowerSeries.coeff_prod]
  simp only [macdonaldKernelFactorU, PowerSeries.coeff_mk]
  simp_rw [prod_monomial, coeff_sum, coeff_monomial]
  rw [← sum_filter]
  have hrow (A : Fin N → Fin N → ℕ) (hA : A ∈ contingencyTables ⇑r ⇑c) :
      ∑ p : Fin N × Fin N, A p.1 p.2 = r.degree := by
    rw [mem_contingencyTables] at hA
    rw [Fintype.sum_prod_type, Finsupp.degree_eq_sum]
    exact sum_congr rfl fun i _ ↦ hA.1 i
  have hbij : ∑ l ∈ (univ.finsuppAntidiag d).filter (fun l : Fin N × Fin N →₀ ℕ ↦
        ∑ p ∈ univ, l p • macdonaldKernelExponent (Fin N) p.1 p.2 = Finsupp.sumElim r c),
        ∏ p ∈ univ, macdonaldGCoeff q t (l p) =
      ∑ A ∈ (contingencyTables ⇑r ⇑c).filter (fun A ↦ ∑ p : Fin N × Fin N, A p.1 p.2 = d),
        ∏ i, ∏ j, macdonaldGCoeff q t (A i j) := by
    refine sum_nbij' (fun l i j ↦ l (i, j))
      (fun A ↦ Finsupp.equivFunOnFinite.symm fun p ↦ A p.1 p.2)
      (fun l hl ↦ ?_) (fun A hA ↦ ?_) (fun l _ ↦ ?_) (fun A _ ↦ ?_) fun l _ ↦ ?_
    · simp only [mem_filter, mem_finsuppAntidiag, subset_univ, and_true] at hl
      simp only [mem_filter, mem_contingencyTables]
      refine ⟨⟨fun i ↦ ?_, fun j ↦ ?_⟩, hl.1⟩
      · exact (sum_nsmul_macdonaldKernelExponent_inl (fun a b ↦ l (a, b)) i).symm.trans
          (congrArg (· (Sum.inl i)) hl.2)
      · exact (sum_nsmul_macdonaldKernelExponent_inr (fun a b ↦ l (a, b)) j).symm.trans
          (congrArg (· (Sum.inr j)) hl.2)
    · simp only [mem_filter, mem_contingencyTables] at hA
      simp only [mem_filter, mem_finsuppAntidiag, subset_univ, and_true]
      refine ⟨by simpa using hA.2, Finsupp.ext fun s ↦ ?_⟩
      have hs : (∑ p : Fin N × Fin N, (Finsupp.equivFunOnFinite.symm fun p : Fin N × Fin N ↦
          A p.1 p.2) p • macdonaldKernelExponent (Fin N) p.1 p.2) =
          ∑ p : Fin N × Fin N, A p.1 p.2 • macdonaldKernelExponent (Fin N) p.1 p.2 :=
        sum_congr rfl fun p _ ↦ by simp
      rw [hs]
      cases s with
      | inl i => rw [sum_nsmul_macdonaldKernelExponent_inl, Finsupp.sumElim_inl, hA.1.1 i]
      | inr j => rw [sum_nsmul_macdonaldKernelExponent_inr, Finsupp.sumElim_inr, hA.1.2 j]
    · exact Finsupp.ext fun p ↦ by simp
    · funext i j
      simp
    · exact Fintype.prod_prod_type fun p : Fin N × Fin N ↦ macdonaldGCoeff q t (l p)
  rw [hbij]
  by_cases hr : r.degree = d
  · rw [filter_true_of_mem fun A hA ↦ (hrow A hA).trans hr]
    by_cases hc : c.degree = d
    · rw [ite_eq_left ⟨hr, hc⟩, macdonaldKernelCoeff]
    · rw [ite_eq_right fun h ↦ hc h.2]
      refine (macdonaldKernelCoeff_eq_zero_of_sum_ne q t ?_)
      rw [← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum, hr]
      exact Ne.symm hc
  · rw [filter_false_of_mem fun A hA h ↦ hr ((hrow A hA).symm.trans h), sum_empty,
      ite_eq_right fun h ↦ hr h.1]

/-- Rescaling the variables in `f(xᵢ yⱼ u)` multiplies its `uⁿ`-coefficient by
`(v(xᵢ) v(yⱼ))ⁿ`. -/
theorem coeff_map_macdonaldKernelFactorU (v : Fin N ⊕ Fin N → K) (q t : K) (i j : Fin N) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.map (scaleVarsBy v : MvPolynomial (Fin N ⊕ Fin N) K →+* _)
        (macdonaldKernelFactorU q t i j)) =
      monomial (n • macdonaldKernelExponent (Fin N) i j)
        (macdonaldGCoeff q t n * (v (Sum.inl i) * v (Sum.inr j)) ^ n) := by
  rw [PowerSeries.coeff_map, macdonaldKernelFactorU, PowerSeries.coeff_mk, RingHom.coe_coe,
    scaleVarsBy_monomial, prod_pow_nsmul_macdonaldKernelExponent]

/-- A rescaling that fixes `xᵢ yⱼ` fixes `f(xᵢ yⱼ u)`. -/
theorem map_macdonaldKernelFactorU_of_mul_eq_one {v : Fin N ⊕ Fin N → K} (q t : K) {i j : Fin N}
    (hv : v (Sum.inl i) * v (Sum.inr j) = 1) :
    PowerSeries.map (scaleVarsBy v : MvPolynomial (Fin N ⊕ Fin N) K →+* _)
        (macdonaldKernelFactorU q t i j) = macdonaldKernelFactorU q t i j :=
  PowerSeries.ext fun n ↦ by
    rw [coeff_map_macdonaldKernelFactorU, hv, one_pow, mul_one, macdonaldKernelFactorU,
      PowerSeries.coeff_mk]

/-- **The `q`-shift of one factor**: if the rescaling multiplies `xᵢ yⱼ` by `q`, then
`f(q xᵢ yⱼ u)(1 - t xᵢ yⱼ u) = f(xᵢ yⱼ u)(1 - xᵢ yⱼ u)`. -/
theorem map_macdonaldKernelFactorU_mul {q : K} (hq : ∀ k, IsUnit (1 - q ^ (k + 1))) (t : K)
    {v : Fin N ⊕ Fin N → K} {i j : Fin N} (hv : v (Sum.inl i) * v (Sum.inr j) = q) :
    PowerSeries.map (scaleVarsBy v : MvPolynomial (Fin N ⊕ Fin N) K →+* _)
        (macdonaldKernelFactorU q t i j) *
        (1 - PowerSeries.C (monomial (macdonaldKernelExponent (Fin N) i j) t) * PowerSeries.X) =
      macdonaldKernelFactorU q t i j *
        (1 - PowerSeries.C (monomial (macdonaldKernelExponent (Fin N) i j) 1) *
          PowerSeries.X) := by
  refine PowerSeries.ext fun n ↦ ?_
  rw [mul_sub, mul_one, mul_sub, mul_one, map_sub, map_sub, mul_left_comm _ (PowerSeries.C _),
    mul_left_comm _ (PowerSeries.C _), PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_zero_mul_X,
      coeff_map_macdonaldKernelFactorU, macdonaldKernelFactorU, PowerSeries.coeff_mk]
    simp
  | succ k =>
    rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_succ_mul_X,
      coeff_map_macdonaldKernelFactorU, coeff_map_macdonaldKernelFactorU, hv,
      macdonaldKernelFactorU, PowerSeries.coeff_mk, PowerSeries.coeff_mk, monomial_mul_monomial,
      monomial_mul_monomial, ← succ_nsmul', ← map_sub, ← map_sub]
    congr 1
    linear_combination -(one_sub_pow_mul_macdonaldGCoeff_succ hq t k)

/-- The linear factor `1 - a xᵢ yⱼ u` in `K[x, y][[u]]`. -/
noncomputable def macdonaldKernelLinear (a : K) (i j : Fin N) :
    PowerSeries (MvPolynomial (Fin N ⊕ Fin N) K) :=
  1 - PowerSeries.C (monomial (macdonaldKernelExponent (Fin N) i j) a) * PowerSeries.X

variable (N) in
/-- The scaling vector of the `q`-shift `T_{q,J}` in the `y` variables: `q` at `yⱼ` for `j ∈ J`
and `1` elsewhere. -/
def macdonaldShiftScaleRight (q : K) (J : Finset (Fin N)) : Fin N ⊕ Fin N → K :=
  Sum.elim (fun _ ↦ 1) fun j ↦ if j ∈ J then q else 1

/-- **The `q`-shift equation in `x`**: `T^x_{q,I} Π · ∏_{i∈I,j} (1 - t xᵢ yⱼ u) =
Π · ∏_{i∈I,j} (1 - xᵢ yⱼ u)`. -/
theorem map_macdonaldKernelU_mul_left {q : K} (hq : ∀ k, IsUnit (1 - q ^ (k + 1))) (t : K)
    (I : Finset (Fin N)) :
    PowerSeries.map (scaleVarsBy (macdonaldShiftScale (Fin N) q I) :
        MvPolynomial (Fin N ⊕ Fin N) K →+* _) (macdonaldKernelU q t) *
        ∏ i ∈ I, ∏ j, macdonaldKernelLinear t i j =
      macdonaldKernelU q t *
        ∏ i ∈ I, ∏ j, macdonaldKernelLinear 1 i j := by
  set φ := (scaleVarsBy (macdonaldShiftScale (Fin N) q I) :
    MvPolynomial (Fin N ⊕ Fin N) K →+* MvPolynomial (Fin N ⊕ Fin N) K)
  have hin : ∀ i ∈ I,
      (∏ j, PowerSeries.map φ (macdonaldKernelFactorU q t i j)) *
          ∏ j, macdonaldKernelLinear t i j =
        (∏ j, macdonaldKernelFactorU q t i j) *
          ∏ j, macdonaldKernelLinear 1 i j := fun i hi ↦ by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun j _ ↦ map_macdonaldKernelFactorU_mul hq t (by
      simp [macdonaldShiftScale, hi])
  have hout : ∀ i ∈ Iᶜ, ∏ j, PowerSeries.map φ (macdonaldKernelFactorU q t i j) =
      ∏ j, macdonaldKernelFactorU q t i j := fun i hi ↦
    prod_congr rfl fun j _ ↦ map_macdonaldKernelFactorU_of_mul_eq_one q t (by
      simp [macdonaldShiftScale, mem_compl.mp hi])
  rw [macdonaldKernelU, map_prod]
  simp_rw [map_prod]
  rw [← prod_mul_prod_compl I,
    ← prod_mul_prod_compl I (fun i ↦ ∏ j, macdonaldKernelFactorU q t i j),
    prod_congr rfl hout, mul_right_comm, ← prod_mul_distrib, prod_congr rfl hin, prod_mul_distrib,
    mul_right_comm]

/-- **The `q`-shift equation in `y`**: `T^y_{q,J} Π · ∏_{j∈J,i} (1 - t xᵢ yⱼ u) =
Π · ∏_{j∈J,i} (1 - xᵢ yⱼ u)`. -/
theorem map_macdonaldKernelU_mul_right {q : K} (hq : ∀ k, IsUnit (1 - q ^ (k + 1))) (t : K)
    (J : Finset (Fin N)) :
    PowerSeries.map (scaleVarsBy (macdonaldShiftScaleRight N q J) :
        MvPolynomial (Fin N ⊕ Fin N) K →+* _) (macdonaldKernelU q t) *
        ∏ j ∈ J, ∏ i, macdonaldKernelLinear t i j =
      macdonaldKernelU q t *
        ∏ j ∈ J, ∏ i, macdonaldKernelLinear 1 i j := by
  set φ := (scaleVarsBy (macdonaldShiftScaleRight N q J) :
    MvPolynomial (Fin N ⊕ Fin N) K →+* MvPolynomial (Fin N ⊕ Fin N) K)
  have hin : ∀ j ∈ J,
      (∏ i, PowerSeries.map φ (macdonaldKernelFactorU q t i j)) *
          ∏ i, macdonaldKernelLinear t i j =
        (∏ i, macdonaldKernelFactorU q t i j) *
          ∏ i, macdonaldKernelLinear 1 i j := fun j hj ↦ by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ ↦ map_macdonaldKernelFactorU_mul hq t (by
      simp [macdonaldShiftScaleRight, hj])
  have hout : ∀ j ∈ Jᶜ, ∏ i, PowerSeries.map φ (macdonaldKernelFactorU q t i j) =
      ∏ i, macdonaldKernelFactorU q t i j := fun j hj ↦
    prod_congr rfl fun i _ ↦ map_macdonaldKernelFactorU_of_mul_eq_one q t (by
      simp [macdonaldShiftScaleRight, mem_compl.mp hj])
  rw [macdonaldKernelU, prod_comm, map_prod]
  simp_rw [map_prod]
  rw [← prod_mul_prod_compl J,
    ← prod_mul_prod_compl J (fun j ↦ ∏ i, macdonaldKernelFactorU q t i j),
    prod_congr rfl hout, mul_right_comm, ← prod_mul_distrib, prod_congr rfl hin, prod_mul_distrib,
    mul_right_comm]

end Series

section Operator

variable {K : Type*} [Field K] {N : ℕ}

/-- The `x`-shift acts on `p(x)` as `scaleVars`. -/
theorem scaleVarsBy_rename_inl (q : K) (I : Finset (Fin N)) (p : MvPolynomial (Fin N) K) :
    scaleVarsBy (macdonaldShiftScale (Fin N) q I) (rename Sum.inl p) =
      rename Sum.inl (scaleVars q I p) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  by_cases hi : i ∈ I <;> simp [scaleVarsBy, macdonaldShiftScale, hi]

/-- The `x`-shift fixes `m(y)`. -/
theorem scaleVarsBy_rename_inr (q : K) (I : Finset (Fin N)) (p : MvPolynomial (Fin N) K) :
    scaleVarsBy (macdonaldShiftScale (Fin N) q I) (rename Sum.inr p) = rename Sum.inr p := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  simp [scaleVarsBy, macdonaldShiftScale]

/-- The `y`-shift acts on `m(y)` as `scaleVars`. -/
theorem scaleVarsBy_right_rename_inr (q : K) (J : Finset (Fin N)) (p : MvPolynomial (Fin N) K) :
    scaleVarsBy (macdonaldShiftScaleRight N q J) (rename Sum.inr p) =
      rename Sum.inr (scaleVars q J p) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  by_cases hi : i ∈ J <;> simp [scaleVarsBy, macdonaldShiftScaleRight, hi]

/-- The `y`-shift fixes `p(x)`. -/
theorem scaleVarsBy_right_rename_inl (q : K) (J : Finset (Fin N)) (p : MvPolynomial (Fin N) K) :
    scaleVarsBy (macdonaldShiftScaleRight N q J) (rename Sum.inl p) = rename Sum.inl p := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  simp [scaleVarsBy, macdonaldShiftScaleRight]

variable [CharZero K]

/-- **`D_x Π_d`**: the `r`-th Macdonald operator applied to the `x`-side of the kernel,
`∑_λ (D g_λ)(x) m_λ(y)`. -/
noncomputable def macdonaldOpLeft (q t : K) (r d : ℕ) : MvPolynomial (Fin N ⊕ Fin N) K :=
  ∑ ν : {ν : d.Partition // ν.parts.card ≤ Fintype.card (Fin N)},
    rename Sum.inl ((macdonaldOp q t r ⟨macdonaldGPart (Fin N) q t ν.1,
        (mem_symmetricSubalgebra _).mpr (macdonaldGPart_isSymmetric q t ν.1)⟩ :
        symmetricSubalgebra (Fin N) K) : MvPolynomial (Fin N) K) *
      rename Sum.inr (msymm (Fin N) K ν.1)

/-- **`D_y Π_d`**: the `r`-th Macdonald operator applied to the `y`-side of the kernel,
`∑_λ g_λ(x) (D m_λ)(y)`. -/
noncomputable def macdonaldOpRight (q t : K) (r d : ℕ) : MvPolynomial (Fin N ⊕ Fin N) K :=
  ∑ ν : {ν : d.Partition // ν.parts.card ≤ Fintype.card (Fin N)},
    rename Sum.inl (macdonaldGPart (Fin N) q t ν.1) *
      rename Sum.inr ((macdonaldOp q t r ⟨msymm (Fin N) K ν.1,
        (mem_symmetricSubalgebra _).mpr (msymm_isSymmetric (Fin N) K ν.1)⟩ :
        symmetricSubalgebra (Fin N) K) : MvPolynomial (Fin N) K)

/-- **The operator identity in `x`**:
`V(x) · D_x Π_d = ∑_{|I|=r} T_{t,I} V(x) · T^x_{q,I} Π_d`. -/
theorem vandermonde_mul_macdonaldOpLeft (q t : K) (r d : ℕ) :
    rename Sum.inl (vandermonde N K) * macdonaldOpLeft q t r d =
      ∑ I ∈ (univ : Finset (Fin N)).powersetCard r,
        rename Sum.inl (scaleVars t I (vandermonde N K)) *
          scaleVarsBy (macdonaldShiftScale (Fin N) q I) (macdonaldKernelPoly q t d) := by
  rw [macdonaldOpLeft, mul_sum, macdonaldKernelPoly]
  simp_rw [map_sum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun ν _ ↦ ?_
  rw [← mul_assoc, ← map_mul, vandermonde_mul_macdonaldOp, macdonaldOpNumerator, map_sum, sum_mul]
  refine sum_congr rfl fun I _ ↦ ?_
  rw [map_mul (scaleVarsBy _), scaleVarsBy_rename_inl, scaleVarsBy_rename_inr,
    map_mul (rename Sum.inl)]
  exact mul_assoc _ _ _

/-- **The operator identity in `y`**:
`V(y) · D_y Π_d = ∑_{|J|=r} T_{t,J} V(y) · T^y_{q,J} Π_d`. -/
theorem vandermonde_mul_macdonaldOpRight (q t : K) (r d : ℕ) :
    rename Sum.inr (vandermonde N K) * macdonaldOpRight q t r d =
      ∑ J ∈ (univ : Finset (Fin N)).powersetCard r,
        rename Sum.inr (scaleVars t J (vandermonde N K)) *
          scaleVarsBy (macdonaldShiftScaleRight N q J) (macdonaldKernelPoly q t d) := by
  rw [macdonaldOpRight, mul_sum, macdonaldKernelPoly]
  simp_rw [map_sum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun ν _ ↦ ?_
  rw [mul_left_comm, ← map_mul, vandermonde_mul_macdonaldOp, macdonaldOpNumerator, map_sum,
    mul_sum]
  refine sum_congr rfl fun J _ ↦ ?_
  rw [map_mul (scaleVarsBy _), scaleVarsBy_right_rename_inl, scaleVarsBy_right_rename_inr,
    map_mul (rename Sum.inr)]
  exact mul_left_comm _ _ _

end Operator

section Combine

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}

variable (N) in
/-- `D_x Π` as a power series in `u`: its `u^d`-coefficient is `D_x Π_d`. -/
noncomputable def macdonaldOpLeftU (q t : K) (r : ℕ) :
    PowerSeries (MvPolynomial (Fin N ⊕ Fin N) K) :=
  PowerSeries.mk fun d ↦ macdonaldOpLeft q t r d

variable (N) in
/-- `D_y Π` as a power series in `u`: its `u^d`-coefficient is `D_y Π_d`. -/
noncomputable def macdonaldOpRightU (q t : K) (r : ℕ) :
    PowerSeries (MvPolynomial (Fin N ⊕ Fin N) K) :=
  PowerSeries.mk fun d ↦ macdonaldOpRight q t r d

variable (N) in
/-- The common denominator `W = ∏_{i,j} (1 - t xᵢ yⱼ u)`. -/
noncomputable def macdonaldKernelDen (t : K) : PowerSeries (MvPolynomial (Fin N ⊕ Fin N) K) :=
  ∏ i, ∏ j, macdonaldKernelLinear t i j

variable (N) in
/-- The polynomial
`Q_x = ∑_{|I|=r} T_{t,I} V(x) ∏_{i∈I,j} (1 - xᵢ yⱼ u) ∏_{i∉I,j} (1 - t xᵢ yⱼ u)`. -/
noncomputable def macdonaldKernelSumLeft (t : K) (r : ℕ) :
    PowerSeries (MvPolynomial (Fin N ⊕ Fin N) K) :=
  ∑ I ∈ (univ : Finset (Fin N)).powersetCard r,
    PowerSeries.C (rename Sum.inl (scaleVars t I (vandermonde N K))) *
      ((∏ i ∈ I, ∏ j, macdonaldKernelLinear 1 i j) * ∏ i ∈ Iᶜ, ∏ j, macdonaldKernelLinear t i j)

variable (N) in
/-- The polynomial
`Q_y = ∑_{|J|=r} T_{t,J} V(y) ∏_{j∈J,i} (1 - xᵢ yⱼ u) ∏_{j∉J,i} (1 - t xᵢ yⱼ u)`. -/
noncomputable def macdonaldKernelSumRight (t : K) (r : ℕ) :
    PowerSeries (MvPolynomial (Fin N ⊕ Fin N) K) :=
  ∑ J ∈ (univ : Finset (Fin N)).powersetCard r,
    PowerSeries.C (rename Sum.inr (scaleVars t J (vandermonde N K))) *
      ((∏ j ∈ J, ∏ i, macdonaldKernelLinear 1 i j) * ∏ j ∈ Jᶜ, ∏ i, macdonaldKernelLinear t i j)

/-- The operator identity in `x`, for the whole series `Π(u)`. -/
theorem C_vandermonde_mul_macdonaldOpLeftU (q t : K) (r : ℕ) :
    PowerSeries.C (rename Sum.inl (vandermonde N K)) * macdonaldOpLeftU N q t r =
      ∑ I ∈ (univ : Finset (Fin N)).powersetCard r,
        PowerSeries.C (rename Sum.inl (scaleVars t I (vandermonde N K))) *
          PowerSeries.map (scaleVarsBy (macdonaldShiftScale (Fin N) q I) :
            MvPolynomial (Fin N ⊕ Fin N) K →+* MvPolynomial (Fin N ⊕ Fin N) K)
            (macdonaldKernelU q t) := by
  refine PowerSeries.ext fun d ↦ ?_
  rw [PowerSeries.coeff_C_mul, macdonaldOpLeftU, PowerSeries.coeff_mk,
    vandermonde_mul_macdonaldOpLeft, map_sum]
  refine sum_congr rfl fun I _ ↦ ?_
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, coeff_macdonaldKernelU, RingHom.coe_coe]

/-- The operator identity in `y`, for the whole series `Π(u)`. -/
theorem C_vandermonde_mul_macdonaldOpRightU (q t : K) (r : ℕ) :
    PowerSeries.C (rename Sum.inr (vandermonde N K)) * macdonaldOpRightU N q t r =
      ∑ J ∈ (univ : Finset (Fin N)).powersetCard r,
        PowerSeries.C (rename Sum.inr (scaleVars t J (vandermonde N K))) *
          PowerSeries.map (scaleVarsBy (macdonaldShiftScaleRight N q J) :
            MvPolynomial (Fin N ⊕ Fin N) K →+* MvPolynomial (Fin N ⊕ Fin N) K)
            (macdonaldKernelU q t) := by
  refine PowerSeries.ext fun d ↦ ?_
  rw [PowerSeries.coeff_C_mul, macdonaldOpRightU, PowerSeries.coeff_mk,
    vandermonde_mul_macdonaldOpRight, map_sum]
  refine sum_congr rfl fun J _ ↦ ?_
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, coeff_macdonaldKernelU, RingHom.coe_coe]

/-- `V(x) · D_x Π · W = Π · Q_x`, by the `q`-shift equation in `x`. -/
theorem C_vandermonde_mul_macdonaldOpLeftU_mul {q : K} (hq : ∀ k, IsUnit (1 - q ^ (k + 1)))
    (t : K) (r : ℕ) :
    PowerSeries.C (rename Sum.inl (vandermonde N K)) * macdonaldOpLeftU N q t r *
        macdonaldKernelDen N t =
      macdonaldKernelU q t * macdonaldKernelSumLeft N t r := by
  rw [C_vandermonde_mul_macdonaldOpLeftU, sum_mul, macdonaldKernelSumLeft, mul_sum]
  refine sum_congr rfl fun I _ ↦ ?_
  rw [macdonaldKernelDen, ← prod_mul_prod_compl I]
  have h := map_macdonaldKernelU_mul_left hq t I
  calc _ = PowerSeries.C (rename Sum.inl (scaleVars t I (vandermonde N K))) *
        (PowerSeries.map (scaleVarsBy (macdonaldShiftScale (Fin N) q I) :
          MvPolynomial (Fin N ⊕ Fin N) K →+* MvPolynomial (Fin N ⊕ Fin N) K)
          (macdonaldKernelU q t) * ∏ i ∈ I, ∏ j, macdonaldKernelLinear t i j) *
        ∏ i ∈ Iᶜ, ∏ j, macdonaldKernelLinear t i j := by ring
    _ = _ := by rw [h]; ring

/-- `V(y) · D_y Π · W = Π · Q_y`, by the `q`-shift equation in `y`. -/
theorem C_vandermonde_mul_macdonaldOpRightU_mul {q : K} (hq : ∀ k, IsUnit (1 - q ^ (k + 1)))
    (t : K) (r : ℕ) :
    PowerSeries.C (rename Sum.inr (vandermonde N K)) * macdonaldOpRightU N q t r *
        macdonaldKernelDen N t =
      macdonaldKernelU q t * macdonaldKernelSumRight N t r := by
  rw [C_vandermonde_mul_macdonaldOpRightU, sum_mul, macdonaldKernelSumRight, mul_sum]
  refine sum_congr rfl fun J _ ↦ ?_
  rw [macdonaldKernelDen, prod_comm, ← prod_mul_prod_compl J]
  have h := map_macdonaldKernelU_mul_right hq t J
  calc _ = PowerSeries.C (rename Sum.inr (scaleVars t J (vandermonde N K))) *
        (PowerSeries.map (scaleVarsBy (macdonaldShiftScaleRight N q J) :
          MvPolynomial (Fin N ⊕ Fin N) K →+* MvPolynomial (Fin N ⊕ Fin N) K)
          (macdonaldKernelU q t) * ∏ j ∈ J, ∏ i, macdonaldKernelLinear t i j) *
        ∏ j ∈ Jᶜ, ∏ i, macdonaldKernelLinear t i j := by ring
    _ = _ := by rw [h]; ring

/-- The factor `1 - a xᵢ yⱼ u` is nonzero: its constant term is `1`. -/
theorem macdonaldKernelLinear_ne_zero (a : K) (i j : Fin N) : macdonaldKernelLinear a i j ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.coeff 0) h
  simp [macdonaldKernelLinear] at this

private theorem macdonaldOpLeft_eq_macdonaldOpRight_of_sum {q : K}
    (hq : ∀ k, IsUnit (1 - q ^ (k + 1))) (t : K) (r : ℕ)
    (hP : PowerSeries.C (rename Sum.inr (vandermonde N K)) * macdonaldKernelSumLeft N t r =
      PowerSeries.C (rename Sum.inl (vandermonde N K)) * macdonaldKernelSumRight N t r)
    (d : ℕ) : macdonaldOpLeft (N := N) q t r d = macdonaldOpRight q t r d := by
  have hV : ∀ f : Fin N → Fin N ⊕ Fin N, Function.Injective f →
      PowerSeries.C (rename f (vandermonde N K)) ≠ 0 := fun f hf h ↦ by
    rw [map_eq_zero_iff _ PowerSeries.C_injective,
      map_eq_zero_iff _ (rename_injective f hf)] at h
    exact vandermonde_ne_zero N K h
  have hW : macdonaldKernelDen N t ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ ↦ prod_ne_zero_iff.mpr fun j _ ↦
      macdonaldKernelLinear_ne_zero t i j
  have hL := C_vandermonde_mul_macdonaldOpLeftU_mul (N := N) hq t r
  have hR := C_vandermonde_mul_macdonaldOpRightU_mul (N := N) hq t r
  have key : (PowerSeries.C (rename Sum.inl (vandermonde N K)) *
      PowerSeries.C (rename Sum.inr (vandermonde N K)) * macdonaldKernelDen N t) *
        macdonaldOpLeftU N q t r =
      (PowerSeries.C (rename Sum.inl (vandermonde N K)) *
        PowerSeries.C (rename Sum.inr (vandermonde N K)) * macdonaldKernelDen N t) *
        macdonaldOpRightU N q t r := by
    calc _ = PowerSeries.C (rename Sum.inr (vandermonde N K)) *
          (PowerSeries.C (rename Sum.inl (vandermonde N K)) * macdonaldOpLeftU N q t r *
            macdonaldKernelDen N t) := by ring
      _ = macdonaldKernelU q t *
          (PowerSeries.C (rename Sum.inr (vandermonde N K)) * macdonaldKernelSumLeft N t r) := by
          rw [hL]; ring
      _ = macdonaldKernelU q t *
          (PowerSeries.C (rename Sum.inl (vandermonde N K)) * macdonaldKernelSumRight N t r) := by
          rw [hP]
      _ = PowerSeries.C (rename Sum.inl (vandermonde N K)) *
          (PowerSeries.C (rename Sum.inr (vandermonde N K)) * macdonaldOpRightU N q t r *
            macdonaldKernelDen N t) := by rw [hR]; ring
      _ = _ := by ring
  have hU := mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hV _ Sum.inl_injective)
    (hV _ Sum.inr_injective)) hW) key
  have := congrArg (PowerSeries.coeff d) hU
  rwa [macdonaldOpLeftU, macdonaldOpRightU, PowerSeries.coeff_mk, PowerSeries.coeff_mk] at this

end Combine

section Identity

/-- `∏_{i∈I} aᵢ · ∏_{i∉I} bᵢ = (∏ bᵢ) · ∏_{i∈I} aᵢ / bᵢ` for double products with nonzero `b`. -/
theorem prod_mul_prod_compl_eq_mul_prod_div {L : Type*} [Field L] {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] (I : Finset ι) (a b : ι → κ → L) (hb : ∀ i j, b i j ≠ 0) :
    (∏ i ∈ I, ∏ j, a i j) * ∏ i ∈ Iᶜ, ∏ j, b i j =
      (∏ i, ∏ j, b i j) * ∏ i ∈ I, ∏ j, a i j / b i j := by
  rw [← prod_mul_prod_compl I (fun i ↦ ∏ j, b i j)]
  have h : ∏ i ∈ I, ∏ j, a i j = (∏ i ∈ I, ∏ j, b i j) * ∏ i ∈ I, ∏ j, a i j / b i j := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ ↦ ?_
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun j _ ↦ ?_
    have := hb i j
    field_simp
  rw [h]
  ring

/-- The monomial `a xᵢ yⱼ`. -/
theorem monomial_macdonaldKernelExponent {K σ : Type*} [CommSemiring K] (a : K) (i j : σ) :
    monomial (macdonaldKernelExponent σ i j) a = C a * X (Sum.inl i) * X (Sum.inr j) := by
  simp only [macdonaldKernelExponent, X, C_apply, monomial_mul_monomial, zero_add, mul_one]

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}

/-- **The kernel identity, polynomial form**: `V(y) · Q_x = V(x) · Q_y`.  This is
`Macdonald.kernelSum_comm` at the point `(x, u y)` of the fraction field of `K[x, y][[u]]`,
multiplied by `V(x) V(y) t^{r(r-1)/2} W`. -/
theorem C_vandermonde_mul_macdonaldKernelSumLeft (t : K) (r : ℕ) :
    PowerSeries.C (rename Sum.inr (vandermonde N K)) * macdonaldKernelSumLeft N t r =
      PowerSeries.C (rename Sum.inl (vandermonde N K)) * macdonaldKernelSumRight N t r := by
  classical
  let L := FractionRing (PowerSeries (MvPolynomial (Fin N ⊕ Fin N) K))
  let φ : PowerSeries (MvPolynomial (Fin N ⊕ Fin N) K) →+* L := algebraMap _ L
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  apply hφ
  let ψ : K →+* L := φ.comp (PowerSeries.C.comp C)
  let x : Fin N → L := fun i ↦ φ (PowerSeries.C (X (Sum.inl i)))
  let y0 : Fin N → L := fun j ↦ φ (PowerSeries.C (X (Sum.inr j)))
  let u : L := φ PowerSeries.X
  let y : Fin N → L := fun j ↦ y0 j * u
  let tL : L := ψ t
  have hlin (a : K) (i j : Fin N) : φ (macdonaldKernelLinear a i j) = 1 - ψ a * x i * y j := by
    simp only [macdonaldKernelLinear, monomial_macdonaldKernelExponent, map_sub, map_one,
      map_mul, ψ, x, y, y0, u, RingHom.comp_apply]
    ring
  have hlin1 (i j : Fin N) : φ (macdonaldKernelLinear 1 i j) = 1 - x i * y j := by
    rw [hlin, map_one, one_mul]
  have hren (f : Fin N → Fin N ⊕ Fin N) (p : MvPolynomial (Fin N) K) :
      φ (PowerSeries.C (rename f p)) = eval (fun i ↦ φ (PowerSeries.C (X (f i)))) (map ψ p) := by
    induction p using MvPolynomial.induction_on with
    | C a => simp [ψ]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, hp, rename_X, map_X, eval_X]
  have hvan : map ψ (vandermonde N K) = vandermonde N L := by
    simp [vandermonde, map_prod]
  have hscale (I : Finset (Fin N)) (p : MvPolynomial (Fin N) K) :
      map ψ (scaleVars t I p) = Nat.PartitionVector.Macdonald.scaleSubset tL I (map ψ p) := by
    have h : (map ψ).comp (scaleVars t I : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) K) =
        (Nat.PartitionVector.Macdonald.scaleSubset tL I :
          MvPolynomial (Fin N) L →+* MvPolynomial (Fin N) L).comp (map ψ) := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) fun i ↦ ?_
      · simp [algHom_C]
      · by_cases hi : i ∈ I
        · simp [scaleVars_X_of_mem _ _ hi, hi, smul_eq_C_mul, tL]
        · simp [scaleVars_X_of_notMem _ _ hi, hi]
    exact RingHom.congr_fun h p
  have hCinj : Function.Injective fun s : Fin N ⊕ Fin N ↦ φ (PowerSeries.C (X s)) :=
    hφ.comp (PowerSeries.C_injective.comp (X_injective (σ := Fin N ⊕ Fin N) (R := K)))
  have hxinj : Function.Injective x := hCinj.comp Sum.inl_injective
  have hy0inj : Function.Injective y0 := hCinj.comp Sum.inr_injective
  have hu : u ≠ 0 := (map_ne_zero_iff φ hφ).mpr PowerSeries.X_ne_zero
  have hyinj : Function.Injective y := fun i j h ↦ hy0inj (mul_right_cancel₀ hu h)
  have hb (i j : Fin N) : 1 - tL * x i * y j ≠ 0 := by
    rw [← hlin]
    exact (map_ne_zero_iff φ hφ).mpr (macdonaldKernelLinear_ne_zero t i j)
  have hvx (I : Finset (Fin N)) :
      φ (PowerSeries.C (rename Sum.inl (scaleVars t I (vandermonde N K)))) =
        eval x (vandermonde N L) * (tL ^ (I.card * (I.card - 1) / 2) *
          ∏ i ∈ I, ∏ j ∈ univ \ I, (tL * x i - x j) / (x i - x j)) := by
    rw [hren, hscale, hvan]
    exact Nat.PartitionVector.Macdonald.eval_scaleSubset_vandermonde tL I x
      fun i j h ↦ sub_ne_zero.mpr (hxinj.ne h)
  have hvy (J : Finset (Fin N)) :
      φ (PowerSeries.C (rename Sum.inr (scaleVars t J (vandermonde N K)))) =
        eval y0 (vandermonde N L) * (tL ^ (J.card * (J.card - 1) / 2) *
          ∏ i ∈ J, ∏ j ∈ univ \ J, (tL * y0 i - y0 j) / (y0 i - y0 j)) := by
    rw [hren, hscale, hvan]
    exact Nat.PartitionVector.Macdonald.eval_scaleSubset_vandermonde tL J y0
      fun i j h ↦ sub_ne_zero.mpr (hy0inj.ne h)
  have hVx : φ (PowerSeries.C (rename Sum.inl (vandermonde N K))) = eval x (vandermonde N L) := by
    rw [hren, hvan]
  have hVy : φ (PowerSeries.C (rename Sum.inr (vandermonde N K))) =
      eval y0 (vandermonde N L) := by
    rw [hren, hvan]
  have hA (J : Finset (Fin N)) :
      ∏ i ∈ J, ∏ j ∈ univ \ J, (tL * y i - y j) / (y i - y j) =
        ∏ i ∈ J, ∏ j ∈ univ \ J, (tL * y0 i - y0 j) / (y0 i - y0 j) :=
    prod_congr rfl fun i _ ↦ prod_congr rfl fun j _ ↦ by
      rw [show tL * y i - y j = (tL * y0 i - y0 j) * u by simp only [y]; ring,
        show y i - y j = (y0 i - y0 j) * u by simp only [y]; ring, mul_div_mul_right _ _ hu]
  have hleft : φ (PowerSeries.C (rename Sum.inr (vandermonde N K)) *
      macdonaldKernelSumLeft N t r) =
      eval x (vandermonde N L) * eval y0 (vandermonde N L) * tL ^ (r * (r - 1) / 2) *
        (∏ i, ∏ j, (1 - tL * x i * y j)) * Macdonald.kernelSum N r tL x y := by
    rw [map_mul, macdonaldKernelSumLeft, map_sum, hVy, Macdonald.kernelSum, mul_sum, mul_sum]
    refine sum_congr rfl fun I hI ↦ ?_
    rw [map_mul, hvx, (mem_powersetCard.mp hI).2, map_mul, map_prod, map_prod]
    simp_rw [map_prod, hlin1, hlin]
    rw [prod_mul_prod_compl_eq_mul_prod_div I (fun i j ↦ 1 - x i * y j)
      (fun i j ↦ 1 - tL * x i * y j) hb]
    ring
  have hright : φ (PowerSeries.C (rename Sum.inl (vandermonde N K)) *
      macdonaldKernelSumRight N t r) =
      eval x (vandermonde N L) * eval y0 (vandermonde N L) * tL ^ (r * (r - 1) / 2) *
        (∏ i, ∏ j, (1 - tL * x i * y j)) * Macdonald.kernelSum N r tL y x := by
    rw [map_mul, macdonaldKernelSumRight, map_sum, hVx, Macdonald.kernelSum, mul_sum, mul_sum]
    refine sum_congr rfl fun J hJ ↦ ?_
    rw [map_mul, hvy, (mem_powersetCard.mp hJ).2, map_mul, map_prod, map_prod, hA]
    simp_rw [map_prod, hlin1, hlin]
    rw [prod_mul_prod_compl_eq_mul_prod_div J (fun j i ↦ 1 - x i * y j)
      (fun j i ↦ 1 - tL * x i * y j) fun j i ↦ hb i j]
    have hW : ∏ j, ∏ i, (1 - tL * x i * y j) = ∏ i, ∏ j, (1 - tL * x i * y j) := prod_comm
    have hB : ∏ i ∈ J, ∏ j, (1 - y i * x j) / (1 - tL * y i * x j) =
        ∏ i ∈ J, ∏ j, (1 - x j * y i) / (1 - tL * x j * y i) :=
      prod_congr rfl fun i _ ↦ prod_congr rfl fun j _ ↦ by
        rw [mul_comm (y i) (x j), mul_right_comm tL (y i) (x j)]
    rw [hW, hB]
    ring
  rw [hleft, hright, Macdonald.kernelSum_comm N r tL x y hxinj hyinj hb]

/-- **`D_x Π_d = D_y Π_d`**: the `r`-th Macdonald operator acting on the `x`-side of the degree-`d`
kernel `∑_λ g_λ(x) m_λ(y)` gives the same polynomial as acting on the `y`-side. -/
theorem macdonaldOpLeft_eq_macdonaldOpRight {q : K} (hq : ∀ k, IsUnit (1 - q ^ (k + 1))) (t : K)
    (r d : ℕ) : macdonaldOpLeft (N := N) q t r d = macdonaldOpRight q t r d :=
  macdonaldOpLeft_eq_macdonaldOpRight_of_sum hq t r (C_vandermonde_mul_macdonaldKernelSumLeft t r) d

end Identity

section Final

/-- `K[x][y] ≃ K[x, y]` sends `p` with constant coefficients to `p(x)`. -/
theorem sumAlgEquiv_symm_map_C {R σ τ : Type*} [CommSemiring R] (p : MvPolynomial σ R) :
    (sumAlgEquiv R σ τ).symm (map C p) = rename Sum.inl p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sumAlgEquiv_symm_C_C]
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]
  | mul_X p i h => simp [h, sumAlgEquiv_symm_X]

/-- `K[x][y] ≃ K[x, y]` sends a constant `m` to `m(y)`. -/
theorem sumAlgEquiv_symm_C_eq_rename {R σ τ : Type*} [CommSemiring R] (p : MvPolynomial τ R) :
    (sumAlgEquiv R σ τ).symm (C p) = rename Sum.inr p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sumAlgEquiv_symm_C_C]
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]
  | mul_X p i h => simp [h, sumAlgEquiv_symm_C_X]

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}

/-- Additivity of `macdonaldOp`, on explicit subtype elements. -/
theorem macdonaldOp_mk_add (q t : K) (r : ℕ) {f g : MvPolynomial (Fin N) K}
    (hf : f ∈ symmetricSubalgebra (Fin N) K) (hg : g ∈ symmetricSubalgebra (Fin N) K)
    (hfg : f + g ∈ symmetricSubalgebra (Fin N) K) :
    (macdonaldOp q t r ⟨f + g, hfg⟩ : MvPolynomial (Fin N) K) =
      (macdonaldOp q t r ⟨f, hf⟩ : MvPolynomial (Fin N) K) + macdonaldOp q t r ⟨g, hg⟩ := by
  have h : (⟨f + g, hfg⟩ : symmetricSubalgebra (Fin N) K) = ⟨f, hf⟩ + ⟨g, hg⟩ :=
    Subtype.ext (by simp)
  rw [h, map_add, Subalgebra.coe_add]

/-- Homogeneity of `macdonaldOp`, on explicit subtype elements. -/
theorem macdonaldOp_mk_smul (q t : K) (r : ℕ) (c : K) {f : MvPolynomial (Fin N) K}
    (hf : f ∈ symmetricSubalgebra (Fin N) K) (hcf : c • f ∈ symmetricSubalgebra (Fin N) K) :
    (macdonaldOp q t r ⟨c • f, hcf⟩ : MvPolynomial (Fin N) K) =
      c • (macdonaldOp q t r ⟨f, hf⟩ : MvPolynomial (Fin N) K) := by
  have h : (⟨c • f, hcf⟩ : symmetricSubalgebra (Fin N) K) = c • ⟨f, hf⟩ :=
    Subtype.ext (by simp)
  rw [h, map_smul, Subalgebra.coe_smul]

omit [CharZero K] in
/-- A symmetric homogeneous polynomial is symmetric. -/
theorem mem_symmetricSubalgebra_of_mem {d : ℕ} (f : symmetricHomogeneousSubmodule (Fin N) K d) :
    (f : MvPolynomial (Fin N) K) ∈ symmetricSubalgebra (Fin N) K :=
  (mem_symmetricSubalgebra _).mpr (mem_symmetricHomogeneousSubmodule.mp f.2).1

/-- **The `r`-th Macdonald operator restricted to the symmetric polynomials of degree `d`**, which
it preserves (`MvPolynomial.IsHomogeneous.macdonaldOp`). -/
noncomputable def macdonaldOpHom (q t : K) (r d : ℕ) :
    symmetricHomogeneousSubmodule (Fin N) K d →ₗ[K] symmetricHomogeneousSubmodule (Fin N) K d where
  toFun f := ⟨(macdonaldOp q t r ⟨f, mem_symmetricSubalgebra_of_mem f⟩ :
      symmetricSubalgebra (Fin N) K),
    mem_symmetricHomogeneousSubmodule.mpr ⟨(mem_symmetricSubalgebra _).mp (macdonaldOp q t r _).2,
      (mem_symmetricHomogeneousSubmodule.mp f.2).2.macdonaldOp q t r⟩⟩
  map_add' f g := Subtype.ext (macdonaldOp_mk_add q t r (mem_symmetricSubalgebra_of_mem f)
    (mem_symmetricSubalgebra_of_mem g) (mem_symmetricSubalgebra_of_mem (f + g)))
  map_smul' c f := Subtype.ext (macdonaldOp_mk_smul q t r c (mem_symmetricSubalgebra_of_mem f)
    (mem_symmetricSubalgebra_of_mem (c • f)))

/-- The restricted operator is `macdonaldOp` on the underlying polynomial. -/
theorem coe_macdonaldOpHom (q t : K) (r d : ℕ) (f : symmetricHomogeneousSubmodule (Fin N) K d)
    (hf : (f : MvPolynomial (Fin N) K) ∈ symmetricSubalgebra (Fin N) K) :
    (macdonaldOpHom q t r d f : MvPolynomial (Fin N) K) =
      (macdonaldOp q t r ⟨f, hf⟩ : symmetricSubalgebra (Fin N) K) :=
  rfl

/-- The restricted operator on a monomial-basis vector is `D m_ν`. -/
theorem coe_macdonaldOpHom_msymmBasis (q t : K) (r d : ℕ)
    (ν : {ν : d.Partition // ν.parts.card ≤ Fintype.card (Fin N)}) :
    (macdonaldOpHom q t r d (msymmBasis (Fin N) K d ν) : MvPolynomial (Fin N) K) =
      (macdonaldOp q t r ⟨msymm (Fin N) K ν.1,
        (mem_symmetricSubalgebra _).mpr (msymm_isSymmetric (Fin N) K ν.1)⟩ :
        symmetricSubalgebra (Fin N) K) := by
  have hm : msymmBasis (Fin N) K d ν =
      ⟨msymm (Fin N) K ν.1, msymm_mem_symmetricHomogeneousSubmodule ν.1⟩ :=
    Subtype.ext (coe_msymmBasis ν)
  rw [hm]
  rfl

private theorem isSelfAdjoint_macdonaldOpHom_of_sum {q t : K} (hq : ∀ k, IsUnit (1 - q ^ (k + 1)))
    {d : ℕ} (h : IsUnit ((msymmBasis (Fin N) K d).det (macdonaldGFamily (Fin N) q t d))) (r : ℕ)
    (hP : PowerSeries.C (rename Sum.inr (vandermonde N K)) * macdonaldKernelSumLeft N t r =
      PowerSeries.C (rename Sum.inl (vandermonde N K)) * macdonaldKernelSumRight N t r) :
    LinearMap.IsSelfAdjoint (macdonaldPairing h) (macdonaldOpHom q t r d) := by
  rw [isSelfAdjoint_macdonaldPairing_iff]
  apply (sumAlgEquiv K (Fin N) (Fin N)).symm.injective
  simp only [map_sum, map_mul, sumAlgEquiv_symm_map_C, sumAlgEquiv_symm_C_eq_rename]
  calc _ = macdonaldOpLeft (N := N) q t r d := sum_congr rfl fun ν _ ↦ rfl
    _ = macdonaldOpRight q t r d := macdonaldOpLeft_eq_macdonaldOpRight_of_sum hq t r hP d
    _ = _ := sum_congr rfl fun ν _ ↦ by rw [coe_macdonaldOpHom_msymmBasis]

/-- **Pieri ledger Lemma 5: the Macdonald operators are self-adjoint.** For `q` with every
`1 - q^{k+1}` a unit and parameters where the `g_λ` form a basis, the restriction of `D_N^r` to the
symmetric polynomials of degree `d` is self-adjoint for the `(q, t)` pairing. -/
theorem isSelfAdjoint_macdonaldOpHom {q t : K} (hq : ∀ k, IsUnit (1 - q ^ (k + 1))) {d : ℕ}
    (h : IsUnit ((msymmBasis (Fin N) K d).det (macdonaldGFamily (Fin N) q t d))) (r : ℕ) :
    LinearMap.IsSelfAdjoint (macdonaldPairing h) (macdonaldOpHom q t r d) :=
  isSelfAdjoint_macdonaldOpHom_of_sum hq h r (C_vandermonde_mul_macdonaldKernelSumLeft t r)

/-- **Self-adjointness for generic `q, t`**: over a field with an injective ring homomorphism
`φ : ℚ[q, t] → K`, with `q = φ (X 0)` and `t = φ (X 1)`. -/
theorem isSelfAdjoint_macdonaldOpHom_of_injective (φ : MvPolynomial (Fin 2) ℚ →+* K)
    (hφ : Function.Injective φ) (r d : ℕ) :
    LinearMap.IsSelfAdjoint
      (macdonaldPairing (isUnit_det_macdonaldGFamily_of_injective (σ := Fin N) (n := d) φ hφ))
      (macdonaldOpHom (φ (X 0)) (φ (X 1)) r d) := by
  refine isSelfAdjoint_macdonaldOpHom (fun k ↦ isUnit_iff_ne_zero.mpr ?_) _ r
  have hne : (1 - X 0 ^ (k + 1) : MvPolynomial (Fin 2) ℚ) ≠ 0 := fun h0 ↦ by
    have := congrArg constantCoeff h0
    simp at this
  simpa using (map_ne_zero_iff φ hφ).mpr hne

end Final

/-- **Self-adjointness over `ℚ(q, t)`.** -/
theorem isSelfAdjoint_macdonaldOpHom_fractionRing (N r d : ℕ) :
    LinearMap.IsSelfAdjoint
      (macdonaldPairing (isUnit_det_macdonaldGFamily_fractionRing (σ := Fin N) (n := d)))
      (macdonaldOpHom (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
        (X 0)) (algebraMap (MvPolynomial (Fin 2) ℚ) (FractionRing (MvPolynomial (Fin 2) ℚ))
        (X 1)) r d) :=
  isSelfAdjoint_macdonaldOpHom_of_injective _ (IsFractionRing.injective _ _) r d

end MvPolynomial
