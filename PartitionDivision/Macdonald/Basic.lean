/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Localization.FractionRing
public import PartitionDivision.Macdonald.Triangular
public import PartitionDivision.Mathlib.LinearAlgebra.Eigenspace.Triangular

/-!
# Macdonald polynomials in finitely many variables

The first Macdonald operator `D = macdonaldOp q t 1` preserves the space of symmetric polynomials
that are homogeneous of degree `n`.  On the monomial basis `m_λ`, indexed by partition vectors of
size `n` and ordered lexicographically, it is triangular with diagonal entries
`macdonaldEigenvalue q t λ`.  When `q` and `t` are algebraically independent over `ℚ`, these
diagonal entries are pairwise distinct, so `D` has a unique eigenvector of the form
`m_λ + (lexicographically lower terms)` for each `λ`, and these eigenvectors form a basis.

Over `K = FractionRing (MvPolynomial (Fin 2) ℚ)` with `q = X 0` and `t = X 1`, this eigenvector is
the Macdonald polynomial `macdonaldP λ`.

## Main declarations

* `MvPolynomial.macdonaldOpRestrict`: the `r`-th operator on homogeneous symmetric polynomials.
* `MvPolynomial.exists_basis_macdonaldOp_eigenvector`: the triangular eigenbasis of `D`.
* `MvPolynomial.existsUnique_macdonaldOp_eigenvector`: uniqueness of the unitriangular
  eigenvector for each `λ`.
* `MvPolynomial.macdonaldP`, `MvPolynomial.macdonaldPBasis`: the Macdonald polynomials over
  `ℚ(q, t)` and the basis they form in each degree.
-/

@[expose] public section

noncomputable section

open Finset

namespace MvPolynomial

variable {N : ℕ} {K : Type*}

/-- A homogeneous symmetric polynomial, regarded as an element of the symmetric subalgebra. -/
def symmetricHomogeneousToSubalgebra [CommSemiring K] (n : ℕ) :
    symmetricHomogeneousSubmodule K (Fin N) n →ₗ[K] symmetricSubalgebra (Fin N) K where
  toFun f := ⟨f, (mem_symmetricHomogeneousSubmodule.mp f.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_symmetricHomogeneousToSubalgebra [CommSemiring K] (n : ℕ)
    (f : symmetricHomogeneousSubmodule K (Fin N) n) :
    (symmetricHomogeneousToSubalgebra n f : MvPolynomial (Fin N) K) = f :=
  rfl

/-- The `r`-th Macdonald operator on the symmetric polynomials of homogeneous degree `n`. -/
def macdonaldOpRestrict [Field K] [CharZero K] (q t : K) (r n : ℕ) :
    symmetricHomogeneousSubmodule K (Fin N) n →ₗ[K]
      symmetricHomogeneousSubmodule K (Fin N) n :=
  LinearMap.codRestrict (symmetricHomogeneousSubmodule K (Fin N) n)
    ((symmetricSubalgebra (Fin N) K).val.toLinearMap ∘ₗ macdonaldOp q t r ∘ₗ
      symmetricHomogeneousToSubalgebra n)
    (fun f ↦ mem_symmetricHomogeneousSubmodule.mpr
      ⟨(macdonaldOp q t r (symmetricHomogeneousToSubalgebra n f)).2,
        IsHomogeneous.macdonaldOp q t r (f := symmetricHomogeneousToSubalgebra n f)
          (mem_symmetricHomogeneousSubmodule.mp f.2).2⟩)

@[simp]
theorem coe_macdonaldOpRestrict [Field K] [CharZero K] (q t : K) (r n : ℕ)
    (f : symmetricHomogeneousSubmodule K (Fin N) n) :
    (macdonaldOpRestrict q t r n f : MvPolynomial (Fin N) K) =
      macdonaldOp q t r (symmetricHomogeneousToSubalgebra n f) :=
  rfl

/-- An element of the symmetric subalgebra is an eigenvector of `macdonaldOp q t r` exactly when
the numerator equation holds with the corresponding scalar. -/
theorem macdonaldOp_eq_smul_iff [Field K] [CharZero K] (q t : K) (r : ℕ)
    (f : symmetricSubalgebra (Fin N) K) (c : K) :
    macdonaldOp q t r f = c • f ↔
      macdonaldOpNumerator q t r (f : MvPolynomial (Fin N) K) =
        c • (vandermonde N K * (f : MvPolynomial (Fin N) K)) := by
  constructor
  · intro h
    rw [← vandermonde_mul_macdonaldOp, h]
    exact mul_smul_comm c (vandermonde N K) (f : MvPolynomial (Fin N) K)
  · intro h
    apply Subtype.ext
    apply vandermonde_mul_injective
    change vandermonde N K * (macdonaldOp q t r f : MvPolynomial (Fin N) K) =
      vandermonde N K * (c • (f : MvPolynomial (Fin N) K))
    rw [vandermonde_mul_macdonaldOp, h, mul_smul_comm]

/-- The partition vectors of size `n` that are lexicographically smaller than `λ`. -/
def lexLowerPartitionVectors (n : ℕ) (lambda : Nat.PartitionVector N) :
    Set (Nat.PartitionVector N) :=
  {mu | partitionVectorDegree mu = n ∧
    toLex (partitionVectorFinsupp mu) < toLex (partitionVectorFinsupp lambda)}

/-- The lexicographic partial order on the partition vectors of a fixed size.  It indexes the
triangular eigenbasis; it is not declared as an instance. -/
@[instance_reducible]
def lexPartialOrder (N n : ℕ) :
    PartialOrder {mu : Nat.PartitionVector N // partitionVectorDegree mu = n} :=
  PartialOrder.lift (fun mu ↦ toLex (partitionVectorFinsupp mu.1)) (by
    intro a b h
    apply Subtype.ext
    apply Nat.PartitionVector.ext
    intro i
    have h' := congrArg (fun x : Lex (Fin N →₀ ℕ) ↦ ofLex x i) h
    simpa using h')

/-- Membership in the span of a set of monomial basis vectors, read in the ambient polynomial
ring. -/
theorem mem_span_msymmVecBasis_image_iff [Field K] {n : ℕ}
    (T : Set {mu : Nat.PartitionVector N // partitionVectorDegree mu = n})
    (x : symmetricHomogeneousSubmodule K (Fin N) n) :
    x ∈ Submodule.span K (msymmVecBasis K N n '' T) ↔
      (x : MvPolynomial (Fin N) K) ∈
        Submodule.span K ((fun mu ↦ msymmVec K mu.1) '' T) := by
  have himage : (symmetricHomogeneousSubmodule K (Fin N) n).subtype ''
      (msymmVecBasis K N n '' T) = (fun mu ↦ msymmVec K mu.1) '' T := by
    rw [Set.image_image]
    simp
  have hmap := Submodule.map_span (symmetricHomogeneousSubmodule K (Fin N) n).subtype
    (msymmVecBasis K N n '' T)
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

/-- The lexicographically lower basis vectors, read in the ambient polynomial ring. -/
theorem image_msymmVec_lexLower [CommSemiring K] {n : ℕ}
    (mu : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n}) :
    (fun nu : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n} ↦
        msymmVec K nu.1) ''
        {nu | toLex (partitionVectorFinsupp nu.1) < toLex (partitionVectorFinsupp mu.1)} =
      msymmVec K '' lexLowerPartitionVectors n mu.1 := by
  ext p
  constructor
  · rintro ⟨nu, hnu, rfl⟩
    exact ⟨nu.1, ⟨nu.2, hnu⟩, rfl⟩
  · rintro ⟨nu, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨nu, h1⟩, h2, rfl⟩

/-- Every Macdonald operator `D^r` is triangular on the monomial basis of each homogeneous
degree, with respect to the lexicographic order, with diagonal `macdonaldEigenvalueR`. -/
theorem macdonaldOpRestrict_msymmVecBasis_sub_mem_span [Field K] [CharZero K] (q t : K)
    (r n : ℕ) (mu : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n}) :
    macdonaldOpRestrict q t r n (msymmVecBasis K N n mu) -
        macdonaldEigenvalueR q t r mu.1 • msymmVecBasis K N n mu ∈
      Submodule.span K (msymmVecBasis K N n ''
        {nu | toLex (partitionVectorFinsupp nu.1) < toLex (partitionVectorFinsupp mu.1)}) := by
  rw [mem_span_msymmVecBasis_image_iff, image_msymmVec_lexLower]
  have hsym : symmetricHomogeneousToSubalgebra n (msymmVecBasis K N n mu) =
      msymmVecSym K mu.1 :=
    Subtype.ext (coe_msymmVecBasis K N n mu)
  have h := macdonaldOp_msymmVec_sub_mem_span q t r mu.1
  rw [mu.2] at h
  simp only [Submodule.coe_sub, Submodule.coe_smul, coe_macdonaldOpRestrict, hsym,
    coe_msymmVecBasis]
  exact h

/-- The first Macdonald operator is triangular on the monomial basis of each homogeneous
degree, with respect to the lexicographic order. -/
theorem macdonaldOpRestrict_one_msymmVecBasis_sub_mem_span [Field K] [CharZero K] (q t : K)
    (n : ℕ) (mu : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n}) :
    macdonaldOpRestrict q t 1 n (msymmVecBasis K N n mu) -
        macdonaldEigenvalue q t mu.1 • msymmVecBasis K N n mu ∈
      Submodule.span K (msymmVecBasis K N n ''
        {nu | toLex (partitionVectorFinsupp nu.1) < toLex (partitionVectorFinsupp mu.1)}) := by
  rw [← macdonaldEigenvalueR_one]
  exact macdonaldOpRestrict_msymmVecBasis_sub_mem_span q t 1 n mu

/-- Algebraic independence of `q` and `t` separates the diagonal entries. -/
theorem macdonaldEigenvalue_ne_of_lexLt [Field K] [CharZero K] [Algebra ℚ K] (q t : K)
    (phi : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] K) (hphi : Function.Injective phi)
    (hq : phi (X (0 : Fin 2)) = q) (ht : phi (X (1 : Fin 2)) = t) {n : ℕ}
    (mu nu : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n})
    (hlt : toLex (partitionVectorFinsupp nu.1) < toLex (partitionVectorFinsupp mu.1)) :
    macdonaldEigenvalue q t nu.1 ≠ macdonaldEigenvalue q t mu.1 := by
  intro heq
  have hfun := macdonaldEigenvalue_injective q t phi hphi hq ht heq
  have hnu : nu = mu := Subtype.ext (Subtype.ext hfun)
  subst hnu
  exact lt_irrefl _ hlt

/-- **Triangular eigenbasis of the first Macdonald operator.**  If `q` and `t` are algebraically
independent over `ℚ`, the symmetric polynomials of homogeneous degree `n` have a basis of
eigenvectors of `macdonaldOp q t 1`, indexed by the partition vectors `λ` of size `n`, whose
`λ`-th member is `m_λ` plus lexicographically lower `m_μ`, with eigenvalue
`macdonaldEigenvalue q t λ`. -/
theorem exists_basis_macdonaldOp_eigenvector [Field K] [CharZero K] [Algebra ℚ K] (q t : K)
    (phi : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] K) (hphi : Function.Injective phi)
    (hq : phi (X (0 : Fin 2)) = q) (ht : phi (X (1 : Fin 2)) = t) (n : ℕ) :
    ∃ c : Module.Basis {mu : Nat.PartitionVector N // partitionVectorDegree mu = n} K
        (symmetricHomogeneousSubmodule K (Fin N) n),
      ∀ mu, (c mu : MvPolynomial (Fin N) K) - msymmVec K mu.1 ∈
          Submodule.span K (msymmVec K '' lexLowerPartitionVectors n mu.1) ∧
        macdonaldOpRestrict q t 1 n (c mu) = macdonaldEigenvalue q t mu.1 • c mu := by
  obtain ⟨c, hc⟩ := @LinearMap.exists_basis_eigenvector_of_triangular K _ _ _ _ _ _
    (lexPartialOrder N n) (msymmVecBasis K N n) (macdonaldOpRestrict q t 1 n)
    (fun mu ↦ macdonaldEigenvalue q t mu.1)
    (macdonaldOpRestrict_one_msymmVecBasis_sub_mem_span q t n)
    (macdonaldEigenvalue_ne_of_lexLt q t phi hphi hq ht)
  refine ⟨c, fun mu ↦ ⟨?_, (hc mu).2⟩⟩
  have h : c mu - msymmVecBasis K N n mu ∈ Submodule.span K (msymmVecBasis K N n ''
      {nu | toLex (partitionVectorFinsupp nu.1) < toLex (partitionVectorFinsupp mu.1)}) :=
    (hc mu).1
  rw [mem_span_msymmVecBasis_image_iff, image_msymmVec_lexLower] at h
  simpa using h

/-- **Uniqueness of the unitriangular eigenvectors.**  If `q` and `t` are algebraically
independent over `ℚ`, then for every partition vector `λ` there is a unique polynomial
`P = m_λ + (lexicographically lower m_μ of the same size)` whose Macdonald numerator is
`macdonaldEigenvalue q t λ • (vandermonde * P)`, that is, with `D P = ε(λ) P`. -/
theorem existsUnique_macdonaldOp_eigenvector [Field K] [CharZero K] [Algebra ℚ K] (q t : K)
    (phi : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] K) (hphi : Function.Injective phi)
    (hq : phi (X (0 : Fin 2)) = q) (ht : phi (X (1 : Fin 2)) = t)
    (lambda : Nat.PartitionVector N) :
    ∃! P : MvPolynomial (Fin N) K,
      P - msymmVec K lambda ∈ Submodule.span K
          (msymmVec K '' lexLowerPartitionVectors (partitionVectorDegree lambda) lambda) ∧
        macdonaldNumerator q t P = macdonaldEigenvalue q t lambda • (vandermonde N K * P) := by
  set n := partitionVectorDegree lambda with hn
  have hspanV : Submodule.span K (msymmVec K '' lexLowerPartitionVectors n lambda) ≤
      symmetricHomogeneousSubmodule K (Fin N) n := by
    rw [Submodule.span_le]
    rintro _ ⟨nu, hnu, rfl⟩
    rw [SetLike.mem_coe, mem_symmetricHomogeneousSubmodule]
    have h := isHomogeneous_msymmVec K nu
    rw [hnu.1] at h
    exact ⟨msymmVec_isSymmetric K nu, h⟩
  have hPV (P : MvPolynomial (Fin N) K)
      (hP : P - msymmVec K lambda ∈
        Submodule.span K (msymmVec K '' lexLowerPartitionVectors n lambda)) :
      P ∈ symmetricHomogeneousSubmodule K (Fin N) n := by
    have hmV : msymmVec K lambda ∈ symmetricHomogeneousSubmodule K (Fin N) n :=
      mem_symmetricHomogeneousSubmodule.mpr
        ⟨msymmVec_isSymmetric K lambda, isHomogeneous_msymmVec K lambda⟩
    have h := (symmetricHomogeneousSubmodule K (Fin N) n).add_mem (hspanV hP) hmV
    rwa [sub_add_cancel] at h
  have heig (P : symmetricHomogeneousSubmodule K (Fin N) n) :
      macdonaldOpRestrict q t 1 n P = macdonaldEigenvalue q t lambda • P ↔
        macdonaldNumerator q t (P : MvPolynomial (Fin N) K) = macdonaldEigenvalue q t lambda •
          (vandermonde N K * (P : MvPolynomial (Fin N) K)) := by
    rw [← macdonaldOpNumerator_one]
    have h := macdonaldOp_eq_smul_iff q t 1 (symmetricHomogeneousToSubalgebra n P)
      (macdonaldEigenvalue q t lambda)
    rw [Subtype.ext_iff, coe_macdonaldOpRestrict, Submodule.coe_smul]
    rw [Subtype.ext_iff] at h
    exact h
  let mu : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n} := ⟨lambda, rfl⟩
  have hlow (Q : symmetricHomogeneousSubmodule K (Fin N) n)
      (hQ : (Q : MvPolynomial (Fin N) K) - msymmVec K lambda ∈
        Submodule.span K (msymmVec K '' lexLowerPartitionVectors n lambda)) :
      Q - msymmVecBasis K N n mu ∈ Submodule.span K (msymmVecBasis K N n ''
        {nu | toLex (partitionVectorFinsupp nu.1) < toLex (partitionVectorFinsupp mu.1)}) := by
    rw [mem_span_msymmVecBasis_image_iff, image_msymmVec_lexLower]
    simpa [mu] using hQ
  obtain ⟨v, hv, huniq⟩ := @LinearMap.exists_unique_eigenvector_of_triangular K _ _ _ _ _ _
    (lexPartialOrder N n) (msymmVecBasis K N n) (macdonaldOpRestrict q t 1 n)
    (fun mu ↦ macdonaldEigenvalue q t mu.1)
    (macdonaldOpRestrict_one_msymmVecBasis_sub_mem_span q t n)
    (macdonaldEigenvalue_ne_of_lexLt q t phi hphi hq ht) mu
  have hv1 : (v : MvPolynomial (Fin N) K) - msymmVec K lambda ∈
      Submodule.span K (msymmVec K '' lexLowerPartitionVectors n lambda) := by
    have h : v - msymmVecBasis K N n mu ∈ Submodule.span K (msymmVecBasis K N n ''
        {nu | toLex (partitionVectorFinsupp nu.1) < toLex (partitionVectorFinsupp mu.1)}) :=
      hv.1
    rw [mem_span_msymmVecBasis_image_iff, image_msymmVec_lexLower] at h
    simpa [mu] using h
  refine ⟨v, ⟨hv1, (heig v).mp hv.2⟩, ?_⟩
  rintro P ⟨hP, hPeig⟩
  have hPv := huniq ⟨P, hPV P hP⟩ ⟨hlow ⟨P, hPV P hP⟩ hP, (heig ⟨P, hPV P hP⟩).mpr hPeig⟩
  exact congrArg Subtype.val hPv

section RationalFunctions

/-- The field `ℚ(q, t)` of rational functions in the Macdonald parameters. -/
local notation "𝕂" => FractionRing (MvPolynomial (Fin 2) ℚ)

/-- The Macdonald parameter `q = X 0` in `ℚ(q, t)`. -/
abbrev macdonaldParamQ : 𝕂 := algebraMap (MvPolynomial (Fin 2) ℚ) 𝕂 (X 0)

/-- The Macdonald parameter `t = X 1` in `ℚ(q, t)`. -/
abbrev macdonaldParamT : 𝕂 := algebraMap (MvPolynomial (Fin 2) ℚ) 𝕂 (X 1)

/-- The parameters `q` and `t` of `ℚ(q, t)` are algebraically independent over `ℚ`. -/
theorem injective_toAlgHom_macdonaldField :
    Function.Injective (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 2) ℚ) 𝕂) := by
  rw [IsScalarTower.coe_toAlgHom']
  exact IsFractionRing.injective _ _

/-- The defining property of the Macdonald polynomials over `ℚ(q, t)`. -/
theorem existsUnique_macdonaldP (lambda : Nat.PartitionVector N) :
    ∃! P : MvPolynomial (Fin N) 𝕂,
      P - msymmVec 𝕂 lambda ∈ Submodule.span 𝕂
          (msymmVec 𝕂 '' lexLowerPartitionVectors (partitionVectorDegree lambda) lambda) ∧
        macdonaldNumerator macdonaldParamQ macdonaldParamT P =
          macdonaldEigenvalue macdonaldParamQ macdonaldParamT lambda •
            (vandermonde N 𝕂 * P) :=
  existsUnique_macdonaldOp_eigenvector macdonaldParamQ macdonaldParamT
    (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 2) ℚ) 𝕂) injective_toAlgHom_macdonaldField
    (IsScalarTower.toAlgHom_apply _ _ _ _) (IsScalarTower.toAlgHom_apply _ _ _ _) lambda

/-- The Macdonald polynomial `P_λ(x; q, t)` in `N` variables, with coefficients in
`ℚ(q, t) = FractionRing (MvPolynomial (Fin 2) ℚ)`, where `q = X 0` and `t = X 1`.  It is the
unique polynomial `m_λ + (lexicographically lower m_μ of the same size)` that is an eigenvector of
the first Macdonald operator. -/
def macdonaldP (lambda : Nat.PartitionVector N) : MvPolynomial (Fin N) 𝕂 :=
  (existsUnique_macdonaldP lambda).exists.choose

/-- `P_λ` is `m_λ` plus lexicographically lower `m_μ` of the same size. -/
theorem macdonaldP_sub_msymmVec_mem_span (lambda : Nat.PartitionVector N) :
    macdonaldP lambda - msymmVec 𝕂 lambda ∈ Submodule.span 𝕂
      (msymmVec 𝕂 '' lexLowerPartitionVectors (partitionVectorDegree lambda) lambda) :=
  (existsUnique_macdonaldP lambda).exists.choose_spec.1

/-- The eigenvalue equation for `P_λ`, written through the Macdonald numerator. -/
theorem macdonaldNumerator_macdonaldP (lambda : Nat.PartitionVector N) :
    macdonaldNumerator macdonaldParamQ macdonaldParamT (macdonaldP lambda) =
      macdonaldEigenvalue macdonaldParamQ macdonaldParamT lambda •
        (vandermonde N 𝕂 * macdonaldP lambda) :=
  (existsUnique_macdonaldP lambda).exists.choose_spec.2

/-- `P_λ` is the only polynomial with the two defining properties. -/
theorem eq_macdonaldP {lambda : Nat.PartitionVector N} {P : MvPolynomial (Fin N) 𝕂}
    (hP : P - msymmVec 𝕂 lambda ∈ Submodule.span 𝕂
      (msymmVec 𝕂 '' lexLowerPartitionVectors (partitionVectorDegree lambda) lambda))
    (hPeig : macdonaldNumerator macdonaldParamQ macdonaldParamT P =
      macdonaldEigenvalue macdonaldParamQ macdonaldParamT lambda • (vandermonde N 𝕂 * P)) :
    P = macdonaldP lambda :=
  (existsUnique_macdonaldP lambda).unique ⟨hP, hPeig⟩
    (existsUnique_macdonaldP lambda).exists.choose_spec

/-- `P_λ` is symmetric and homogeneous of degree `|λ|`. -/
theorem macdonaldP_mem_symmetricHomogeneousSubmodule (lambda : Nat.PartitionVector N) :
    macdonaldP lambda ∈ symmetricHomogeneousSubmodule 𝕂 (Fin N) (partitionVectorDegree lambda) := by
  have hspan : Submodule.span 𝕂 (msymmVec 𝕂 ''
      lexLowerPartitionVectors (partitionVectorDegree lambda) lambda) ≤
      symmetricHomogeneousSubmodule 𝕂 (Fin N) (partitionVectorDegree lambda) := by
    rw [Submodule.span_le]
    rintro _ ⟨nu, hnu, rfl⟩
    rw [SetLike.mem_coe, mem_symmetricHomogeneousSubmodule]
    have h := isHomogeneous_msymmVec 𝕂 nu
    rw [hnu.1] at h
    exact ⟨msymmVec_isSymmetric 𝕂 nu, h⟩
  have hm : msymmVec 𝕂 lambda ∈
      symmetricHomogeneousSubmodule 𝕂 (Fin N) (partitionVectorDegree lambda) :=
    mem_symmetricHomogeneousSubmodule.mpr
      ⟨msymmVec_isSymmetric 𝕂 lambda, isHomogeneous_msymmVec 𝕂 lambda⟩
  have h := Submodule.add_mem _ (hspan (macdonaldP_sub_msymmVec_mem_span lambda)) hm
  rwa [sub_add_cancel] at h

/-- `P_λ` is symmetric. -/
theorem macdonaldP_isSymmetric (lambda : Nat.PartitionVector N) :
    (macdonaldP lambda).IsSymmetric :=
  (mem_symmetricHomogeneousSubmodule.mp
    (macdonaldP_mem_symmetricHomogeneousSubmodule lambda)).1

/-- `P_λ` is homogeneous of degree `|λ|`. -/
theorem isHomogeneous_macdonaldP (lambda : Nat.PartitionVector N) :
    (macdonaldP lambda).IsHomogeneous (partitionVectorDegree lambda) :=
  (mem_symmetricHomogeneousSubmodule.mp
    (macdonaldP_mem_symmetricHomogeneousSubmodule lambda)).2

/-- `P_λ` is an eigenvector of the first Macdonald operator with eigenvalue
`Σ_i q ^ λ i t ^ (N - 1 - i)`. -/
theorem macdonaldOp_macdonaldP (lambda : Nat.PartitionVector N) :
    macdonaldOp macdonaldParamQ macdonaldParamT 1
        ⟨macdonaldP lambda, macdonaldP_isSymmetric lambda⟩ =
      macdonaldEigenvalue macdonaldParamQ macdonaldParamT lambda •
        (⟨macdonaldP lambda, macdonaldP_isSymmetric lambda⟩ :
          symmetricSubalgebra (Fin N) 𝕂) := by
  rw [macdonaldOp_eq_smul_iff, macdonaldOpNumerator_one]
  exact macdonaldNumerator_macdonaldP lambda

/-- The eigenbasis of the first Macdonald operator on the homogeneous symmetric polynomials of
degree `n`; its members are the Macdonald polynomials (`coe_macdonaldPBasis`). -/
def macdonaldPBasis (N n : ℕ) :
    Module.Basis {mu : Nat.PartitionVector N // partitionVectorDegree mu = n} 𝕂
      (symmetricHomogeneousSubmodule 𝕂 (Fin N) n) :=
  (exists_basis_macdonaldOp_eigenvector macdonaldParamQ macdonaldParamT
    (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 2) ℚ) 𝕂) injective_toAlgHom_macdonaldField
    (IsScalarTower.toAlgHom_apply _ _ _ _) (IsScalarTower.toAlgHom_apply _ _ _ _) n).choose

/-- The members of `macdonaldPBasis` are the Macdonald polynomials. -/
@[simp]
theorem coe_macdonaldPBasis (N n : ℕ)
    (mu : {mu : Nat.PartitionVector N // partitionVectorDegree mu = n}) :
    (macdonaldPBasis N n mu : MvPolynomial (Fin N) 𝕂) = macdonaldP mu.1 := by
  have hspec := (exists_basis_macdonaldOp_eigenvector macdonaldParamQ macdonaldParamT
    (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 2) ℚ) 𝕂) injective_toAlgHom_macdonaldField
    (IsScalarTower.toAlgHom_apply _ _ _ _) (IsScalarTower.toAlgHom_apply _ _ _ _) n).choose_spec
    mu
  obtain ⟨hlow, heig⟩ := hspec
  apply eq_macdonaldP
  · rw [mu.2]
    exact hlow
  · have h := congrArg Subtype.val heig
    rw [coe_macdonaldOpRestrict, Submodule.coe_smul] at h
    have h' := (macdonaldOp_eq_smul_iff macdonaldParamQ macdonaldParamT 1
      (symmetricHomogeneousToSubalgebra n (macdonaldPBasis N n mu))
      (macdonaldEigenvalue macdonaldParamQ macdonaldParamT mu.1)).mp (Subtype.ext h)
    rw [macdonaldOpNumerator_one] at h'
    exact h'

end RationalFunctions

end MvPolynomial
