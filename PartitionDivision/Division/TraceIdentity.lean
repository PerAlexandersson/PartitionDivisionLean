/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Mathlib.RingTheory.MvPolynomial.ExponentFilter
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Trace identity for abstract multiplication matrices

This file proves the root-of-unity trace identity from an abstract family of multiplication
matrices.  No Macdonald-polynomial facts are used.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace PartitionDivision

open MvPolynomial Matrix

variable {F : Type*} [Field F]

private theorem rootTwist_esymm_one_injective {k N : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ k) :
    Function.Injective (fun a : Fin N → Fin k ↦ rootTwist ζ a (esymm (Fin N) F 1)) := by
  classical
  intro a b hab
  funext i
  apply Fin.ext
  apply hζ.pow_inj (Fin.isLt (a i)) (Fin.isLt (b i))
  have hcoeff (c : Fin N → Fin k) :
      (rootTwist ζ c (esymm (Fin N) F 1)).coeff (Finsupp.single i 1) = ζ ^ (c i).val := by
    rw [esymm_one, map_sum]
    simp only [rootTwist, aeval_X]
    change (MvPolynomial.coeffAddMonoidHom (Finsupp.single i 1))
      (∑ x, C (ζ ^ (c x).val) * X x) = _
    rw [map_sum, Finset.sum_eq_single i]
    · change (C (ζ ^ (c i).val) * X i).coeff (Finsupp.single i 1) = _
      rw [coeff_C_mul, coeff_X_same, mul_one]
    · intro j _ hji
      change (C (ζ ^ (c j).val) * X j).coeff (Finsupp.single i 1) = 0
      rw [coeff_C_mul, coeff_X, ite_eq_right]
      · exact mul_zero _
      · exact fun h ↦ hji (Finsupp.single_left_injective one_ne_zero h)
    · simp
  rw [← hcoeff a, ← hcoeff b]
  exact congrArg (fun p : MvPolynomial (Fin N) F ↦ p.coeff (Finsupp.single i 1)) hab

/-- The trace of any product of abstract multiplication matrices is the root-of-unity exponent
filter of the corresponding product of elementary symmetric polynomials. -/
theorem trace_reverse_list_prod_eq_exponentFilter [CharZero F] {k N : ℕ} (hk : 0 < k)
    {ζ : F} (hζ : IsPrimitiveRoot ζ k) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = k ^ N) (o : ι) (B : ι → MvPolynomial (Fin N) F)
    (hBo : B o = 1) (M : ℕ → Matrix ι ι (MvPolynomial (Fin N) F))
    (hM : ∀ r t,
      esymm (Fin N) F r * B t =
        ∑ τ, aeval (fun i : Fin N ↦ expand k (esymm (Fin N) F (i + 1)))
          (M r τ t) * B τ)
    (μ : List ℕ) :
    trace ((μ.map fun r ↦ (M r).map
      (aeval fun i : Fin N ↦ expand k (esymm (Fin N) F (i + 1)))).reverse.prod) =
      (k ^ N : F) • exponentFilter k ((μ.map fun r ↦ esymm (Fin N) F r).prod) := by
  classical
  let _ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let R := MvPolynomial (Fin N) F
  let L := FractionRing R
  let φ : R →ₐ[F] R :=
    aeval fun i : Fin N ↦ expand k (esymm (Fin N) F (i + 1))
  let J := Fin (Fintype.card (Fin N → Fin k))
  let e : (Fin N → Fin k) ≃ J := Fintype.equivFin _
  let α : R →+* L := algebraMap R L
  let A : ℕ → Matrix ι ι L := fun r ↦ ((M r).map φ).map α
  let s : ℕ → J → L := fun r j ↦ α (rootTwist ζ (e.symm j) (esymm (Fin N) F r))
  let D : ℕ → Matrix J J L := fun r ↦ diagonal (s r)
  let U : Matrix J ι L := fun j t ↦ α (rootTwist ζ (e.symm j) (B t))
  have hφ (a : Fin N → Fin k) (p : R) : rootTwist ζ a (φ p) = φ p := by
    change ((rootTwist ζ a).comp φ) p = φ p
    apply congrArg (fun g : R →ₐ[F] R ↦ g p)
    change (rootTwist ζ a).comp φ = φ
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, aeval_X, φ]
    rw [rootTwist, aeval_expand]
    change aeval _ (esymm (Fin N) F (i + 1)) =
      aeval (fun j ↦ X j ^ k) (esymm (Fin N) F (i + 1))
    apply congrArg (fun g : R →ₐ[F] R ↦ g (esymm (Fin N) F (i + 1)))
    apply MvPolynomial.algHom_ext
    intro j
    simp only [aeval_X]
    change (C (ζ ^ (a j).val) * X j) ^ k = _
    rw [mul_pow, ← map_pow, ← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow,
      map_one, one_mul]
  have hDU (r : ℕ) : D r * U = U * A r := by
    ext j t
    have hm := congrArg (α ∘ rootTwist ζ (e.symm j)) (hM r t)
    rw [show D r = diagonal (s r) from rfl, Matrix.diagonal_mul, Matrix.mul_apply]
    change
      α (rootTwist ζ (e.symm j) (esymm (Fin N) F r)) *
          α (rootTwist ζ (e.symm j) (B t)) =
        ∑ x, α (rootTwist ζ (e.symm j) (B x)) * α (φ (M r x t))
    simp only [Function.comp_apply, map_mul, map_sum] at hm
    change
      α (rootTwist ζ (e.symm j) (esymm (Fin N) F r)) *
          α (rootTwist ζ (e.symm j) (B t)) =
        ∑ x, α (rootTwist ζ (e.symm j) (φ (M r x t))) *
          α (rootTwist ζ (e.symm j) (B x)) at hm
    calc
      _ = ∑ x, α (rootTwist ζ (e.symm j) (φ (M r x t))) *
          α (rootTwist ζ (e.symm j) (B x)) := hm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hφ, mul_comm]
  have hUo (j : J) : U j o = 1 := by
    simp [U, hBo]
  have hcardJ : Fintype.card J = Fintype.card ι := by
    simpa [J] using hcard.symm
  let C : Matrix ι J L := fun t j ↦ (A 1 ^ j.val) t o
  have hUA_pow (n : ℕ) : U * A 1 ^ n = D 1 ^ n * U := by
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          U * A 1 ^ (n + 1) = (U * A 1 ^ n) * A 1 := by rw [pow_succ, Matrix.mul_assoc]
          _ = (D 1 ^ n * U) * A 1 := by rw [ih]
          _ = D 1 ^ n * (U * A 1) := by rw [Matrix.mul_assoc]
          _ = D 1 ^ n * (D 1 * U) := by rw [hDU]
          _ = D 1 ^ (n + 1) * U := by rw [pow_succ, Matrix.mul_assoc]
  have hUC : U * C = Matrix.vandermonde (s 1) := by
    ext j n
    rw [Matrix.mul_apply]
    change (U * A 1 ^ n.val) j o = _
    rw [hUA_pow]
    change (D 1 ^ n.val * U) j o = (s 1 j) ^ n.val
    rw [show D 1 = diagonal (s 1) from rfl, Matrix.diagonal_pow,
      Matrix.diagonal_mul, hUo, mul_one]
    exact Pi.pow_apply _ _ _
  have hs : Function.Injective (s 1) := by
    intro i j hij
    apply e.symm.injective
    apply rootTwist_esymm_one_injective hζ
    apply IsFractionRing.injective R L
    exact hij
  have hdet : (U * C).det ≠ 0 := by
    rw [hUC, Matrix.det_vandermonde_ne_zero_iff]
    exact hs
  have hunit : IsUnit (U * C).det := isUnit_iff_ne_zero.mpr hdet
  let V : Matrix ι J L := C * (U * C)⁻¹
  have hUV : U * V = 1 := by
    change U * (C * (U * C)⁻¹) = 1
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit]
  have hVU : V * U = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq J ι L hcardJ).mp hUV
  have hintertwine (l : List ℕ) :
      U * (l.map A).prod = (l.map D).prod * U := by
    induction l with
    | nil => simp
    | cons r l ih =>
        simp only [List.map_cons, List.prod_cons]
        calc
          U * (A r * (l.map A).prod) = (U * A r) * (l.map A).prod := by
            rw [Matrix.mul_assoc]
          _ = (D r * U) * (l.map A).prod := by rw [hDU]
          _ = D r * (U * (l.map A).prod) := by rw [Matrix.mul_assoc]
          _ = D r * ((l.map D).prod * U) := by rw [ih]
          _ = (D r * (l.map D).prod) * U := by rw [Matrix.mul_assoc]
  have htrace (l : List ℕ) : trace (l.map A).prod = trace (l.map D).prod := by
    calc
      trace (l.map A).prod = trace (V * U * (l.map A).prod) := by rw [hVU, Matrix.one_mul]
      _ = trace (V * (U * (l.map A).prod)) := by rw [Matrix.mul_assoc]
      _ = trace ((U * (l.map A).prod) * V) := Matrix.trace_mul_comm _ _
      _ = trace ((l.map D).prod * (U * V)) := by rw [hintertwine, Matrix.mul_assoc]
      _ = trace (l.map D).prod := by rw [hUV, Matrix.mul_one]
  have hdiag (l : List ℕ) :
      (l.map D).prod = diagonal (fun j ↦ (l.map fun r ↦ s r j).prod) := by
    induction l with
    | nil => simp
    | cons r l ih =>
        simp only [List.map_cons, List.prod_cons, ih, D]
        exact Matrix.diagonal_mul_diagonal _ _
  have hmap (l : List (Matrix ι ι R)) :
      l.prod.map α = (l.map fun X ↦ X.map α).prod := by
    induction l with
    | nil => simp
    | cons X l ih => simp [List.prod_cons, ih, Matrix.map_mul]
  apply IsFractionRing.injective R L
  rw [AddMonoidHom.map_trace]
  rw [hmap]
  simp only [List.map_reverse, List.map_map]
  change trace ((μ.map fun r ↦ ((M r).map φ).map α).reverse.prod) = _
  rw [show (fun r ↦ ((M r).map φ).map α) = A from rfl]
  rw [← List.map_reverse]
  rw [htrace, hdiag, trace_diagonal]
  simp only [List.map_reverse]
  simp_rw [List.prod_reverse]
  change
    (∑ x : J, (μ.map fun r ↦ α (rootTwist ζ (e.symm x) (esymm (Fin N) F r))).prod) = _
  let f : R := (μ.map fun r ↦ esymm (Fin N) F r).prod
  have hprod (a : Fin N → Fin k) :
      (μ.map fun r ↦ α (rootTwist ζ a (esymm (Fin N) F r))).prod =
        α (rootTwist ζ a f) := by
    induction μ with
    | nil => simp [f]
    | cons r μ ih => simp [f, ih]
  calc
    (∑ x : J, (μ.map fun r ↦ α (rootTwist ζ (e.symm x)
        (esymm (Fin N) F r))).prod) =
        ∑ a : Fin N → Fin k,
          (μ.map fun r ↦ α (rootTwist ζ a (esymm (Fin N) F r))).prod :=
      e.symm.sum_comp (fun a : Fin N → Fin k ↦
        (μ.map fun r ↦ α (rootTwist ζ a (esymm (Fin N) F r))).prod)
    _ = ∑ a : Fin N → Fin k, α (rootTwist ζ a f) := by
      apply Finset.sum_congr rfl
      intro a _
      exact hprod a
    _ = α (∑ a : Fin N → Fin k, rootTwist ζ a f) := by rw [map_sum]
    _ = α ((k ^ N) • exponentFilter k f) := by
      rw [sum_rootTwist_eq_nsmul_exponentFilter hζ]
      simp
    _ = α ((k ^ N : F) • exponentFilter k f) := by
      congr 1
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

end PartitionDivision
