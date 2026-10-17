/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Self-adjoint operators that are triangular in an eigenbasis

Eigenvectors of an operator that is self-adjoint for a bilinear form, with distinct eigenvalues,
are orthogonal. If such eigenvectors form a basis and the form is nondegenerate, every other
self-adjoint operator that is triangular in that basis is diagonal in it. This is the linear
algebra that makes the Macdonald polynomials joint eigenvectors of all `D_N^r`.

The proofs were found by Aristotle (Harmonic) and ported to this Mathlib version.
-/

@[expose] public section

namespace LinearMap.BilinForm

open Submodule

/-- Eigenvectors of a self-adjoint operator for a symmetric bilinear form, with distinct
eigenvalues, are orthogonal. -/
theorem orthogonal_of_isEigenbasis
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (f : V →ₗ[K] V)
    (hf : ∀ v w, B (f v) w = B v (f w))
    (P : ι → V) (d : ι → K) (hP : ∀ i, f (P i) = d i • P i)
    (hd : Function.Injective d) {i j : ι} (hij : i ≠ j) :
    B (P i) (P j) = 0 := by
  have h1 := hf (P i) (P j)
  rw [hP, hP, LinearMap.map_smul₂, LinearMap.map_smul] at h1
  simp only [smul_eq_mul] at h1
  have h2 : (d i - d j) * B (P i) (P j) = 0 := by rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (hd (sub_eq_zero.mp h)) hij
  · exact h

/-- If `P` is a basis of eigenvectors of a self-adjoint `f` with distinct eigenvalues for a
nondegenerate symmetric form, then any self-adjoint `g` that is triangular with respect to `P`
(for some linear order on the finite index type) is diagonal in `P`. -/
theorem eigenvector_of_triangular_of_selfAdjoint
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite ι] [LinearOrder ι]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (f g : V →ₗ[K] V)
    (hf : ∀ v w, B (f v) w = B v (f w)) (hg : ∀ v w, B (g v) w = B v (g w))
    (P : Module.Basis ι K V) (d : ι → K) (hP : ∀ i, f (P i) = d i • P i)
    (hd : Function.Injective d)
    (hgt : ∀ i, g (P i) ∈ span K (P '' {j | j ≤ i})) (i : ι) :
    ∃ c : K, g (P i) = c • P i := by
  cases nonempty_fintype ι
  have orth : ∀ a b : ι, a ≠ b → B (P a) (P b) = 0 := fun a b hab =>
    orthogonal_of_isEigenbasis B f hf P d hP hd hab
  have expand : ∀ (x : V) (w : V), B x w = ∑ l, P.repr x l * B (P l) w := by
    intro x w
    calc B x w = B (∑ l, P.repr x l • P l) w := by rw [P.sum_repr]
      _ = _ := by
        simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have expand2 : ∀ (v : V) (x : V), B v x = ∑ l, P.repr x l * B v (P l) := by
    intro v x
    calc B v x = B v (∑ l, P.repr x l • P l) := by rw [P.sum_repr]
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  have supp : ∀ (k l : ι), k < l → P.repr (g (P k)) l = 0 := by
    intro k l hkl
    have := (P.mem_span_image).mp (hgt k)
    by_contra hne
    have hl : l ∈ ((P.repr (g (P k))).support : Set ι) := by
      simpa using hne
    have := this hl
    simp only [Set.mem_ofPred_eq] at this
    exact absurd hkl (not_lt.mpr this)
  have diag_ne : ∀ j, B (P j) (P j) ≠ 0 := by
    intro j hj
    have hzero : B (P j) = 0 := by
      refine P.ext fun l => ?_
      by_cases hl : j = l
      · subst hl; simpa using hj
      · simpa using orth j l hl
    exact P.ne_zero j (hB.1 (P j) (fun n => by rw [hzero]; rfl))
  have key : ∀ j, j ≠ i → P.repr (g (P i)) j = 0 := by
    intro j hji
    rcases lt_or_gt_of_ne hji with hlt | hgt'
    · have e1 : B (g (P i)) (P j) = P.repr (g (P i)) j * B (P j) (P j) := by
        rw [expand, Finset.sum_eq_single j]
        · intro l _ hl; rw [orth l j hl, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have e2 : B (P i) (g (P j)) = 0 := by
        rw [expand2]
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hl : l ≤ j
        · rw [orth i l (by intro h; subst h; exact absurd (lt_of_le_of_lt hl hlt) (lt_irrefl _)),
            mul_zero]
        · rw [supp j l (lt_of_not_ge hl), zero_mul]
      rw [hg, e2] at e1
      rcases mul_eq_zero.mp e1.symm with h | h
      · exact h
      · exact absurd h (diag_ne j)
    · exact supp i j hgt'
  refine ⟨P.repr (g (P i)) i, P.repr.injective ?_⟩
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · rw [key j hj]; simp [Ne.symm hj]

end LinearMap.BilinForm
