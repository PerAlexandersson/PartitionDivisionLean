/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Macdonald.PieriInduction
public import PartitionDivision.Macdonald.SelfAdjoint
public import PartitionDivision.Mathlib.LinearAlgebra.SesquilinearForm.SelfAdjointTriangular

/-!
# The joint spectral action of the Macdonald operators (Pieri ledger Lemma 7)

Over `ℚ(q, t)`, every Macdonald operator `D_N^r` acts diagonally on the Macdonald polynomials:
`D_N^r P_λ = ε_r(λ) P_λ`, where `ε_r(λ) = e_r(q^{λ_i} t^{N-1-i})`
(`MvPolynomial.macdonaldOp_macdonaldP_eq_smul`).  In numerator form this is
`Macdonald.MacdonaldJointEigen` (`Macdonald.macdonaldJointEigen`), the hypothesis of
`Macdonald.macdonaldP_normalized_symmetry_and_pieri_of_jointEigen`.

## The argument

Fix a degree `n` and order the partition vectors of size `n` lexicographically.
* The `P_λ` form a basis of eigenvectors of `D^1` with pairwise distinct eigenvalues.
* `D^r` is self-adjoint for the `(q, t)` pairing (`MvPolynomial.isSelfAdjoint_macdonaldOpHom`),
  which is nondegenerate.
* `D^r` is triangular in the monomial basis, `D^r m_λ ∈ ε_r(λ) m_λ + span{m_μ : μ < λ}`.
  `P_λ ∈ m_λ + span{m_μ : μ < λ}`, so `D^r` is also triangular in the basis `P`.

The Aristotle lemma `LinearMap.BilinForm.eigenvector_of_triangular_of_selfAdjoint` then makes `P_λ`
an eigenvector of `D^r`. Comparing the coefficients of `m_λ` identifies the eigenvalue.
-/

@[expose] public section

noncomputable section

open Finset

local notation "𝕂" => FractionRing (MvPolynomial (Fin 2) ℚ)

namespace MvPolynomial

section Triangular

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι]

private theorem map_mem_span_image_of_triangular (T : V →ₗ[K] V) (b : ι → V)
    (hT : ∀ μ, T (b μ) ∈ Submodule.span K (b '' {ν | ν ≤ μ})) (S : Set ι)
    (hS : ∀ μ ∈ S, ∀ ν ≤ μ, ν ∈ S) {x : V} (hx : x ∈ Submodule.span K (b '' S)) :
    T x ∈ Submodule.span K (b '' S) := by
  have h : Submodule.map T (Submodule.span K (b '' S)) ≤ Submodule.span K (b '' S) := by
    rw [Submodule.map_span_le]
    rintro _ ⟨μ, hμ, rfl⟩
    exact Submodule.span_mono (Set.image_mono fun ν hν ↦ hS μ hμ ν hν) (hT μ)
  exact h (Submodule.mem_map_of_mem hx)

private theorem mem_span_image_Iic_of_sub_mem [WellFoundedLT ι] (b P : ι → V)
    (h : ∀ μ, P μ - b μ ∈ Submodule.span K (b '' {ν | ν < μ})) (μ : ι) :
    b μ ∈ Submodule.span K (P '' {ν | ν ≤ μ}) := by
  induction μ using WellFoundedLT.induction with
  | _ μ ih =>
    rw [show b μ = P μ - (P μ - b μ) by abel]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨μ, le_refl μ, rfl⟩) ?_
    refine (Submodule.span_le.mpr ?_) (h μ)
    rintro _ ⟨ν, hν, rfl⟩
    exact Submodule.span_mono (Set.image_mono fun k hk ↦ le_trans hk (le_of_lt hν)) (ih ν hν)

private theorem eq_smul_of_triangular_of_selfAdjoint [Finite ι] (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (f g : V →ₗ[K] V) (hf : ∀ v w, B (f v) w = B v (f w))
    (hg : ∀ v w, B (g v) w = B v (g w)) (P b : Module.Basis ι K V) (d c : ι → K)
    (hP : ∀ i, f (P i) = d i • P i) (hd : Function.Injective d)
    (hgb : ∀ i, g (b i) - c i • b i ∈ Submodule.span K (b '' {j | j < i}))
    (hPb : ∀ i, P i - b i ∈ Submodule.span K (b '' {j | j < i})) (i : ι) :
    g (P i) = c i • P i := by
  have hgb' (j : ι) : g (b j) ∈ Submodule.span K (b '' {k | k ≤ j}) := by
    rw [show g (b j) = (g (b j) - c j • b j) + c j • b j by abel]
    exact Submodule.add_mem _ (Submodule.span_mono (Set.image_mono Set.Iio_subset_Iic_self)
      (hgb j)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, le_refl j, rfl⟩))
  have hPin (j : ι) : P j ∈ Submodule.span K (b '' {k | k ≤ j}) := by
    rw [show P j = b j + (P j - b j) by abel]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨j, le_refl j, rfl⟩)
      (Submodule.span_mono (Set.image_mono Set.Iio_subset_Iic_self) (hPb j))
  have hgt (j : ι) : g (P j) ∈ Submodule.span K (P '' {k | k ≤ j}) := by
    have h1 := map_mem_span_image_of_triangular g b hgb' {k | k ≤ j}
      (fun μ hμ ν hν ↦ le_trans hν hμ) (hPin j)
    refine (Submodule.span_le.mpr ?_) h1
    rintro _ ⟨ν, hν, rfl⟩
    exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.mpr hν))
      (mem_span_image_Iic_of_sub_mem b P hPb ν)
  obtain ⟨a, ha⟩ := LinearMap.BilinForm.eigenvector_of_triangular_of_selfAdjoint B hB f g hf hg P
    d hP hd hgt i
  have hrepr0 {x : V} (hx : x ∈ Submodule.span K (b '' {j | j < i})) : b.repr x i = 0 := by
    by_contra hne
    exact lt_irrefl i ((b.mem_span_image.mp hx) (Finsupp.mem_support_iff.mpr hne))
  have hPrepr : b.repr (P i) i = 1 := by
    rw [show P i = b i + (P i - b i) by abel, map_add, Finsupp.add_apply, hrepr0 (hPb i),
      b.repr_self, Finsupp.single_eq_same, add_zero]
  have hlow : g (P i - b i) ∈ Submodule.span K (b '' {j | j < i}) :=
    map_mem_span_image_of_triangular g b hgb' {j | j < i}
      (fun μ hμ ν hν ↦ lt_of_le_of_lt hν hμ) (hPb i)
  have hsplit : g (P i) = (g (b i) - c i • b i) + c i • b i + g (P i - b i) := by
    rw [map_sub g (P i) (b i)]
    abel
  have hgrepr : b.repr (g (P i)) i = c i := by
    rw [hsplit, map_add, map_add, map_smul, Finsupp.add_apply, Finsupp.add_apply,
      Finsupp.smul_apply, hrepr0 (hgb i), hrepr0 hlow, b.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, zero_add, add_zero]
  have hac : a = c i := by
    rw [← hgrepr, ha, map_smul, Finsupp.smul_apply, hPrepr, smul_eq_mul, mul_one]
  rw [ha, hac]

end Triangular

section Joint

variable {N : ℕ}

/-- The lexicographic linear order on the partition vectors of size `n`, through their exponent
vectors.  It is not declared as an instance. -/
@[instance_reducible]
def lexLinearOrder (N n : ℕ) :
    LinearOrder {mu : Nat.PartitionVector N // partitionVectorDegree mu = n} :=
  LinearOrder.lift' (fun mu ↦ toLex (partitionVectorFinsupp mu.1)) fun _ _ h ↦
    Subtype.ext (partitionVectorFinsupp_injective (toLex.injective h))

attribute [local instance] lexLinearOrder

/-- **`D^r` acts diagonally on the Macdonald basis** in each degree, with eigenvalue `ε_r(λ)`. -/
theorem macdonaldOpRestrict_macdonaldPBasis (r n : ℕ)
    (mu : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n}) :
    macdonaldOpRestrict macdonaldParamQ macdonaldParamT r n (macdonaldPBasis N n mu) =
      macdonaldEigenvalueR macdonaldParamQ macdonaldParamT r mu.1 • macdonaldPBasis N n mu := by
  have hS : MvPolynomial.symmetricHomogeneousSubmodule 𝕂 (Fin N) n =
      TauCeti.symmetricHomogeneousSubmodule (Fin N) 𝕂 n := by
    ext f
    rw [MvPolynomial.mem_symmetricHomogeneousSubmodule, TauCeti.mem_symmetricHomogeneousSubmodule]
  let e : MvPolynomial.symmetricHomogeneousSubmodule 𝕂 (Fin N) n ≃ₗ[𝕂]
      TauCeti.symmetricHomogeneousSubmodule (Fin N) 𝕂 n := LinearEquiv.ofEq _ _ hS
  have hdet := isUnit_det_macdonaldGFamily_fractionRing (σ := Fin N) (n := n)
  let B : LinearMap.BilinForm 𝕂 (MvPolynomial.symmetricHomogeneousSubmodule 𝕂 (Fin N) n) :=
    (macdonaldPairing hdet).compl₁₂ e.toLinearMap e.toLinearMap
  have hB : B.Nondegenerate := by
    obtain ⟨hl, hr⟩ := nondegenerate_macdonaldPairing hdet
    refine ⟨fun x hx ↦ e.injective ?_, fun y hy ↦ e.injective ?_⟩
    · rw [map_zero]
      exact hl (e x) fun y' ↦ by simpa [B] using hx (e.symm y')
    · rw [map_zero]
      exact hr (e y) fun x' ↦ by simpa [B] using hy (e.symm x')
  have hsa (s : ℕ) (v w : MvPolynomial.symmetricHomogeneousSubmodule 𝕂 (Fin N) n) :
      B (macdonaldOpRestrict macdonaldParamQ macdonaldParamT s n v) w =
        B v (macdonaldOpRestrict macdonaldParamQ macdonaldParamT s n w) :=
    isSelfAdjoint_macdonaldOpHom_fractionRing N s n (e v) (e w)
  have hsub (nu : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n}) :
      symmetricHomogeneousToSubalgebra n (macdonaldPBasis N n nu) =
        ⟨macdonaldP nu.1, macdonaldP_isSymmetric nu.1⟩ :=
    Subtype.ext (coe_macdonaldPBasis N n nu)
  have hP (nu : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n}) :
      macdonaldOpRestrict macdonaldParamQ macdonaldParamT 1 n (macdonaldPBasis N n nu) =
        macdonaldEigenvalue macdonaldParamQ macdonaldParamT nu.1 • macdonaldPBasis N n nu := by
    apply Subtype.ext
    rw [Submodule.coe_smul, coe_macdonaldPBasis, coe_macdonaldOpRestrict, hsub,
      macdonaldOp_macdonaldP]
    rfl
  have hd : Function.Injective fun nu : {mu : Nat.PartitionVector N //
      partitionVectorDegree mu = n} ↦ macdonaldEigenvalue macdonaldParamQ macdonaldParamT nu.1 :=
    fun _ _ h ↦ Subtype.ext (Subtype.ext (macdonaldEigenvalue_injective macdonaldParamQ
      macdonaldParamT (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 2) ℚ) 𝕂)
      injective_toAlgHom_macdonaldField (IsScalarTower.toAlgHom_apply _ _ _ _)
      (IsScalarTower.toAlgHom_apply _ _ _ _) h))
  have hPb (nu : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n}) :
      macdonaldPBasis N n nu - msymmVecBasis 𝕂 N n nu ∈
        Submodule.span 𝕂 (msymmVecBasis 𝕂 N n '' {ν | ν < nu}) := by
    rw [show {ν | ν < nu} = {ν : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n} |
      toLex (partitionVectorFinsupp ν.1) < toLex (partitionVectorFinsupp nu.1)} from rfl,
      mem_span_msymmVecBasis_image_iff, image_msymmVec_lexLower]
    have h := macdonaldP_sub_msymmVec_mem_span nu.1
    rw [nu.2] at h
    simpa using h
  exact eq_smul_of_triangular_of_selfAdjoint B hB
    (macdonaldOpRestrict macdonaldParamQ macdonaldParamT 1 n)
    (macdonaldOpRestrict macdonaldParamQ macdonaldParamT r n) (hsa 1) (hsa r)
    (macdonaldPBasis N n) (msymmVecBasis 𝕂 N n)
    (fun nu ↦ macdonaldEigenvalue macdonaldParamQ macdonaldParamT nu.1)
    (fun nu ↦ macdonaldEigenvalueR macdonaldParamQ macdonaldParamT r nu.1) hP hd
    (macdonaldOpRestrict_msymmVecBasis_sub_mem_span macdonaldParamQ macdonaldParamT r n)
    hPb mu

/-- **Pieri ledger Lemma 7: the joint spectral action.**  Every Macdonald operator `D_N^r` has
`P_λ` as an eigenvector, with eigenvalue `ε_r(λ) = e_r(q^{λ_i} t^{N-1-i})`. -/
theorem macdonaldOp_macdonaldP_eq_smul (lambda : Nat.PartitionVector N) (r : ℕ) :
    macdonaldOp macdonaldParamQ macdonaldParamT r
        ⟨macdonaldP lambda, macdonaldP_isSymmetric lambda⟩ =
      macdonaldEigenvalueR macdonaldParamQ macdonaldParamT r lambda •
        (⟨macdonaldP lambda, macdonaldP_isSymmetric lambda⟩ : symmetricSubalgebra (Fin N) 𝕂) := by
  have h := congrArg Subtype.val (macdonaldOpRestrict_macdonaldPBasis (N := N) r
    (partitionVectorDegree lambda) ⟨lambda, rfl⟩)
  have hsub : symmetricHomogeneousToSubalgebra (partitionVectorDegree lambda)
      (macdonaldPBasis N (partitionVectorDegree lambda) ⟨lambda, rfl⟩) =
        ⟨macdonaldP lambda, macdonaldP_isSymmetric lambda⟩ :=
    Subtype.ext (coe_macdonaldPBasis _ _ _)
  rw [coe_macdonaldOpRestrict, Submodule.coe_smul, coe_macdonaldPBasis, hsub] at h
  exact Subtype.ext h

end Joint

end MvPolynomial

namespace Macdonald

open MvPolynomial

variable {N : ℕ}

/-- **`MacdonaldJointEigen` holds**: the numerator form of Lemma 7, as required by
`macdonaldP_normalized_symmetry_and_pieri_of_jointEigen`. -/
theorem macdonaldJointEigen : MacdonaldJointEigen (N := N) := by
  intro lambda r
  exact (macdonaldOp_eq_smul_iff macdonaldParamQ macdonaldParamT r
    ⟨macdonaldP lambda, macdonaldP_isSymmetric lambda⟩
    (macdonaldEigenvalueR macdonaldParamQ macdonaldParamT r lambda)).mp
    (macdonaldOp_macdonaldP_eq_smul lambda r)

/-- **Evaluation symmetry and normalized Pieri, conditional only on Lemma 8**: the hypothesis
`MacdonaldJointEigen` of `macdonaldP_normalized_symmetry_and_pieri_of_jointEigen` is discharged by
`macdonaldJointEigen`. -/
theorem macdonaldP_normalized_symmetry_and_pieri_of_base_ne_zero
    (hne : ∀ lambda : Nat.PartitionVector N, eval (pieriGrid 0) (macdonaldP lambda) ≠ 0) :
    (∀ mu : Nat.PartitionVector N, eval (pieriGrid 0) (macdonaldPNormalized mu) = 1) ∧
      (∀ lambda mu : Nat.PartitionVector N,
        eval (pieriGrid lambda) (macdonaldPNormalized mu) =
          eval (pieriGrid mu) (macdonaldPNormalized lambda)) ∧
      ∀ (mu : Nat.PartitionVector N) (s : ℕ),
        macdonaldPNormalized mu * esymm (Fin N) 𝕂 s =
          ∑ nu ∈ stripSuccessors mu s, stripCoeff mu s nu • macdonaldPNormalized nu :=
  macdonaldP_normalized_symmetry_and_pieri_of_jointEigen macdonaldJointEigen hne

end Macdonald
