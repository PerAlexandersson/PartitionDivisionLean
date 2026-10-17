/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import PartitionDivision.Macdonald.GridDeterminant
public import PartitionDivision.Mathlib.RingTheory.MvPolynomial.Symmetric.Monomial
public import Mathlib.Data.DFinsupp.WellFounded
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Lexicographically unitriangular families of symmetric polynomials

A symmetric polynomial `f` in `N` variables is *lex-unitriangular with leading index `λ`* when
its coefficient at the monomial `x ^ λ` is one and its coefficients at the monomials `x ^ μ`,
for partition vectors `μ` lexicographically above `λ`, vanish.  For a symmetric polynomial this
says exactly that `f = m_λ + Σ_{μ <_lex λ} c_μ m_μ` in the monomial symmetric basis, where
`m_λ = orbitSum λ X`; see `isLexUnitriangular_of_eq_orbitSum_add`.

The main results are:

* `lexUnitriangularBasis`: a family of lex-unitriangular polynomials, one for each partition
  vector, is a basis of the symmetric subalgebra over any commutative ring;
* `mem_range_map_of_isLexUnitriangular`: *regularity*.  Let `O → K` be injective.  If the
  `O`-span of a lex-unitriangular family over `K` is stable under multiplication by every
  elementary symmetric polynomial, then every member of the family has all its coefficients in
  `O`.  The proof writes the monomial symmetric polynomial `m_λ` in the `O`-span (fundamental
  theorem of symmetric polynomials over `O`) and inverts the triangular expansion by induction
  on the lexicographic order.

The regularity theorem is the abstract form of the shortcut in `docs/PIERI.md`, Section 2.  It
needs no analysis of individual Pieri chains: the triangularity of the expansion of `m_λ`
follows from the triangularity of the family itself.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace PartitionDivision.Macdonald

open MvPolynomial Nat.PartitionVector

variable {N : ℕ}

/-- The lexicographic key of a partition vector. -/
def lexKey (lam : Nat.PartitionVector N) : Lex (Fin N → ℕ) := toLex (lam : Fin N → ℕ)

/-- Distinct partition vectors have distinct lexicographic keys. -/
theorem lexKey_injective : Function.Injective (lexKey (N := N)) := by
  intro lam mu h
  exact Nat.PartitionVector.ext fun i ↦ congrFun (toLex.injective h) i

/-- The strict lexicographic order on partition vectors is well founded. -/
theorem wellFounded_lexKey :
    WellFounded fun mu lam : Nat.PartitionVector N ↦ lexKey mu < lexKey lam :=
  InvImage.wf lexKey wellFounded_lt

/-- The empty partition vector is lexicographically smallest. -/
theorem lexKey_zero_le (lam : Nat.PartitionVector N) : lexKey 0 ≤ lexKey lam :=
  Pi.toLex_monotone fun i ↦ Nat.zero_le (lam i)

/-- The exponent map from partition vectors to finitely supported vectors is injective. -/
theorem partitionVectorFinsupp_injective :
    Function.Injective (partitionVectorFinsupp (N := N)) := by
  intro lam mu h
  exact Nat.PartitionVector.ext fun i ↦ by
    simpa using congrArg (fun d : Fin N →₀ ℕ ↦ d i) h

/-- The exponent vector of the empty partition vector is zero. -/
@[simp]
theorem partitionVectorFinsupp_zero : partitionVectorFinsupp (0 : Nat.PartitionVector N) = 0 := by
  ext i
  simp

section OrbitSum

variable (R : Type*) [CommSemiring R]

/-- The orbit sum of `GridDeterminant`, evaluated at the variables, is the monomial symmetric
polynomial `msymmVec`. -/
theorem orbitSum_X_eq_msymmVec (lam : Nat.PartitionVector N) :
    orbitSum lam (X : Fin N → MvPolynomial (Fin N) R) = msymmVec R lam := by
  classical
  have hmon (β : Fin N → ℕ) :
      (∏ i, (X i : MvPolynomial (Fin N) R) ^ β i) =
        monomial (Finsupp.equivFunOnFinite.symm β) 1 := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
    simp
  have himage : lam.rearrangements.image Finsupp.equivFunOnFinite.symm =
      partitionVectorRearrangements lam := by
    ext d
    simp only [Finset.mem_image, rearrangements, Finset.mem_univ, true_and,
      mem_partitionVectorRearrangements_iff]
    constructor
    · rintro ⟨β, ⟨σ, rfl⟩, rfl⟩
      refine ⟨σ.symm, ?_⟩
      ext i
      simp [Finsupp.mapDomain_equiv_apply]
    · rintro ⟨e, rfl⟩
      refine ⟨_, ⟨e.symm, rfl⟩, ?_⟩
      ext i
      simp [Finsupp.mapDomain_equiv_apply]
  rw [orbitSum, msymmVec, ← himage, Finset.sum_image
    (fun _ _ _ _ h ↦ Finsupp.equivFunOnFinite.symm.injective h)]
  exact Finset.sum_congr rfl fun β _ ↦ hmon β

/-- The orbit sum at the variables is symmetric. -/
theorem orbitSum_X_isSymmetric (lam : Nat.PartitionVector N) :
    (orbitSum lam (X : Fin N → MvPolynomial (Fin N) R)).IsSymmetric := by
  rw [orbitSum_X_eq_msymmVec]
  exact msymmVec_isSymmetric R lam

/-- At a partition-vector exponent, the coefficients of orbit sums are Kronecker deltas. -/
theorem coeff_orbitSum_X (lam mu : Nat.PartitionVector N) :
    (orbitSum mu (X : Fin N → MvPolynomial (Fin N) R)).coeff (partitionVectorFinsupp lam) =
      if lam = mu then 1 else 0 := by
  rw [orbitSum_X_eq_msymmVec, coeff_msymmVec_partitionVectorFinsupp]

/-- Coefficient maps commute with orbit sums at the variables. -/
theorem map_orbitSum_X {S : Type*} [CommSemiring S] (f : R →+* S)
    (lam : Nat.PartitionVector N) :
    map f (orbitSum lam (X : Fin N → MvPolynomial (Fin N) R)) = orbitSum lam X := by
  rw [orbitSum_X_eq_msymmVec, orbitSum_X_eq_msymmVec, msymmVec, msymmVec, map_sum]
  simp

end OrbitSum

section Unitriangular

variable {R : Type*} [CommRing R]

/-- A symmetric polynomial whose coefficients vanish at every partition-vector exponent is
zero. -/
theorem eq_zero_of_isSymmetric_of_coeff_eq_zero {f : MvPolynomial (Fin N) R}
    (hf : f.IsSymmetric)
    (h : ∀ mu : Nat.PartitionVector N, f.coeff (partitionVectorFinsupp mu) = 0) :
    f = 0 := by
  ext d
  let g : Fin N → ℕᵒᵈ := fun i ↦ OrderDual.toDual (d i)
  let σ := Tuple.sort g
  have hanti : Antitone ((d : Fin N → ℕ) ∘ σ) :=
    monotone_toDual_comp_iff.mp (Tuple.monotone_sort g)
  let mu : Nat.PartitionVector N := ⟨(d : Fin N → ℕ) ∘ σ, hanti⟩
  have hmu : d.mapDomain σ.symm = partitionVectorFinsupp mu := by
    ext i
    rw [partitionVectorFinsupp_apply, Finsupp.mapDomain_equiv_apply, Equiv.symm_symm]
    rfl
  have hc := coeff_rename_mapDomain σ.symm σ.symm.injective f d
  rw [hf σ.symm, hmu, h mu] at hc
  simp [← hc]

/-- A symmetric polynomial `f` is *lex-unitriangular with leading index `lam`* when its
coefficient at `x ^ lam` is one and its coefficients at `x ^ mu` vanish for every partition
vector `mu` lexicographically greater than `lam`.  For symmetric polynomials this is the
statement `f = m_lam + Σ_{mu <_lex lam} c_mu m_mu`. -/
structure IsLexUnitriangular (f : MvPolynomial (Fin N) R) (lam : Nat.PartitionVector N) :
    Prop where
  /-- The polynomial is symmetric. -/
  isSymmetric : f.IsSymmetric
  /-- The leading coefficient is one. -/
  coeff_self : f.coeff (partitionVectorFinsupp lam) = 1
  /-- Coefficients at lexicographically larger partition vectors vanish. -/
  coeff_eq_zero_of_lt :
    ∀ mu : Nat.PartitionVector N, lexKey lam < lexKey mu →
      f.coeff (partitionVectorFinsupp mu) = 0

/-- The orbit-sum form of unitriangularity implies the coefficient form. -/
theorem isLexUnitriangular_of_eq_orbitSum_add {f : MvPolynomial (Fin N) R}
    {lam : Nat.PartitionVector N} (s : Finset (Nat.PartitionVector N))
    (c : Nat.PartitionVector N → R) (hs : ∀ mu ∈ s, lexKey mu < lexKey lam)
    (hf : f = orbitSum lam X + ∑ mu ∈ s, c mu • orbitSum mu X) :
    IsLexUnitriangular f lam := by
  classical
  have hcoeff (nu : Nat.PartitionVector N) (hnu : lexKey lam ≤ lexKey nu) :
      f.coeff (partitionVectorFinsupp nu) = if nu = lam then 1 else 0 := by
    rw [hf]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_sum, coeff_smul,
      coeff_orbitSum_X]
    rw [Finset.sum_eq_zero, add_zero]
    intro mu hmu
    have hne : nu ≠ mu := by
      rintro rfl
      exact (hs nu hmu).not_ge hnu
    simp [hne]
  refine ⟨?_, ?_, ?_⟩
  · rw [hf]
    refine (orbitSum_X_isSymmetric R lam).add ?_
    rw [← mem_symmetricSubalgebra]
    exact Subalgebra.sum_mem _ fun mu _ ↦ Subalgebra.smul_mem _
      ((mem_symmetricSubalgebra _).mpr (orbitSum_X_isSymmetric R mu)) _
  · simp [hcoeff lam le_rfl]
  · intro mu hmu
    have hne : mu ≠ lam := by
      rintro rfl
      exact hmu.false
    simp [hcoeff mu hmu.le, hne]

/-- A lex-unitriangular polynomial with leading index `0` is the constant one. -/
theorem IsLexUnitriangular.eq_one {f : MvPolynomial (Fin N) R}
    (hf : IsLexUnitriangular f 0) : f = 1 := by
  rw [← sub_eq_zero]
  refine eq_zero_of_isSymmetric_of_coeff_eq_zero (hf.isSymmetric.sub IsSymmetric.one) ?_
  intro mu
  by_cases hmu : mu = 0
  · subst mu
    have h := hf.coeff_self
    rw [partitionVectorFinsupp_zero] at h ⊢
    simp [h]
  · have hlt : lexKey 0 < lexKey mu :=
      (lexKey_zero_le mu).lt_of_ne fun h ↦ hmu (lexKey_injective h).symm
    have hne : (0 : Fin N →₀ ℕ) ≠ partitionVectorFinsupp mu := by
      intro h
      apply hmu
      apply partitionVectorFinsupp_injective
      rw [← h, partitionVectorFinsupp_zero]
    classical
    simp [hf.coeff_eq_zero_of_lt mu hlt, coeff_one, hne]

/-- Every finitely supported coefficient vector with nonempty support has a lexicographically
largest index in its support. -/
theorem exists_lexKey_max_of_ne_zero {M : Type*} [Zero M] {c : Nat.PartitionVector N →₀ M}
    (hc : c ≠ 0) :
    ∃ mu ∈ c.support, ∀ eta ∈ c.support, eta ≠ mu → lexKey eta < lexKey mu := by
  obtain ⟨mu, hmu, hmax⟩ :=
    Finset.exists_max_image c.support lexKey (Finsupp.support_nonempty_iff.mpr hc)
  exact ⟨mu, hmu, fun eta heta hne ↦
    (hmax eta heta).lt_of_ne fun h ↦ hne (lexKey_injective h)⟩

/-- Every polynomial whose coefficients at partition-vector exponents do not all vanish has a
lexicographically largest partition-vector exponent with nonzero coefficient. -/
theorem exists_lexKey_max_coeff_ne_zero (f : MvPolynomial (Fin N) R)
    (hf : ∃ mu : Nat.PartitionVector N, f.coeff (partitionVectorFinsupp mu) ≠ 0) :
    ∃ mu : Nat.PartitionVector N, f.coeff (partitionVectorFinsupp mu) ≠ 0 ∧
      ∀ nu : Nat.PartitionVector N, f.coeff (partitionVectorFinsupp nu) ≠ 0 →
        lexKey nu ≤ lexKey mu := by
  let s : Finset (Nat.PartitionVector N) :=
    f.support.preimage partitionVectorFinsupp partitionVectorFinsupp_injective.injOn
  have hs (nu : Nat.PartitionVector N) : nu ∈ s ↔ f.coeff (partitionVectorFinsupp nu) ≠ 0 := by
    simp [s]
  obtain ⟨mu0, hmu0⟩ := hf
  obtain ⟨mu, hmu, hmax⟩ := Finset.exists_max_image s lexKey ⟨mu0, (hs mu0).mpr hmu0⟩
  exact ⟨mu, (hs mu).mp hmu, fun nu hnu ↦ hmax nu ((hs nu).mpr hnu)⟩

/-- The coefficient of a linear combination of a lex-unitriangular family at the leading index of
a lexicographically largest summand is the image of its coefficient. -/
theorem coeff_sum_smul_of_isLexUnitriangular {O : Type*} [CommRing O] [Algebra O R]
    {P : Nat.PartitionVector N → MvPolynomial (Fin N) R}
    (hP : ∀ lam, IsLexUnitriangular (P lam) lam) (c : Nat.PartitionVector N →₀ O)
    {mu : Nat.PartitionVector N}
    (hmu : ∀ eta ∈ c.support, eta ≠ mu → lexKey eta < lexKey mu) :
    (c.sum fun eta a ↦ a • P eta).coeff (partitionVectorFinsupp mu) = algebraMap O R (c mu) := by
  rw [Finsupp.sum, coeff_sum]
  simp_rw [coeff_smul]
  simp_rw [Algebra.smul_def]
  by_cases hmem : mu ∈ c.support
  · rw [Finset.sum_eq_single mu]
    · rw [(hP mu).coeff_self, mul_one]
    · intro eta heta hne
      rw [(hP eta).coeff_eq_zero_of_lt mu (hmu eta heta hne), mul_zero]
    · exact fun h ↦ (h hmem).elim
  · rw [Finsupp.notMem_support_iff.mp hmem, map_zero]
    apply Finset.sum_eq_zero
    intro eta heta
    have hne : eta ≠ mu := fun h ↦ hmem (h ▸ heta)
    rw [(hP eta).coeff_eq_zero_of_lt mu (hmu eta heta hne), mul_zero]

variable {P : Nat.PartitionVector N → MvPolynomial (Fin N) R}

/-- A lex-unitriangular family is linearly independent. -/
theorem linearIndependent_of_isLexUnitriangular (hP : ∀ lam, IsLexUnitriangular (P lam) lam) :
    LinearIndependent R P := by
  rw [linearIndependent_iff]
  intro c hc
  by_contra hne
  obtain ⟨mu, hmu, hmax⟩ := exists_lexKey_max_of_ne_zero hne
  have h := coeff_sum_smul_of_isLexUnitriangular (O := R) hP c hmax
  rw [Finsupp.linearCombination_apply] at hc
  rw [hc, Algebra.algebraMap_self, RingHom.id_apply] at h
  exact Finsupp.mem_support_iff.mp hmu (by simpa using h.symm)

/-- The members of a lex-unitriangular family, as elements of the symmetric subalgebra. -/
def lexUnitriangularFamily (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (lam : Nat.PartitionVector N) : symmetricSubalgebra (Fin N) R :=
  ⟨P lam, (mem_symmetricSubalgebra _).mpr (hP lam).isSymmetric⟩

private theorem mem_span_of_lexKey_le (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (mu : Nat.PartitionVector N) :
    ∀ x : symmetricSubalgebra (Fin N) R,
      (∀ nu : Nat.PartitionVector N,
        (x : MvPolynomial (Fin N) R).coeff (partitionVectorFinsupp nu) ≠ 0 →
          lexKey nu ≤ lexKey mu) →
      x ∈ Submodule.span R (Set.range (lexUnitriangularFamily hP)) := by
  induction mu using wellFounded_lexKey.induction with
  | _ mu ih =>
  intro x hx
  set c := (x : MvPolynomial (Fin N) R).coeff (partitionVectorFinsupp mu)
  set y := x - c • lexUnitriangularFamily hP mu
  have hxy : x = y + c • lexUnitriangularFamily hP mu := by simp [y]
  have hmem : c • lexUnitriangularFamily hP mu ∈
      Submodule.span R (Set.range (lexUnitriangularFamily hP)) :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨mu, rfl⟩)
  have hycoeff (nu : Nat.PartitionVector N) :
      (y : MvPolynomial (Fin N) R).coeff (partitionVectorFinsupp nu) =
        (x : MvPolynomial (Fin N) R).coeff (partitionVectorFinsupp nu) -
          c * (P mu).coeff (partitionVectorFinsupp nu) := by
    simp [y, lexUnitriangularFamily]
  have hylt (nu : Nat.PartitionVector N)
      (hnu : (y : MvPolynomial (Fin N) R).coeff (partitionVectorFinsupp nu) ≠ 0) :
      lexKey nu < lexKey mu := by
    rcases lt_trichotomy (lexKey nu) (lexKey mu) with h | h | h
    · exact h
    · rw [lexKey_injective h] at hnu
      rw [hycoeff, (hP mu).coeff_self, mul_one, sub_self] at hnu
      exact (hnu rfl).elim
    · have hx0 : (x : MvPolynomial (Fin N) R).coeff (partitionVectorFinsupp nu) = 0 := by
        by_contra hne
        exact (hx nu hne).not_gt h
      rw [hycoeff, hx0, (hP mu).coeff_eq_zero_of_lt nu h, mul_zero, sub_zero] at hnu
      exact (hnu rfl).elim
  rw [hxy]
  refine Submodule.add_mem _ ?_ hmem
  by_cases hy : ∃ nu : Nat.PartitionVector N,
      (y : MvPolynomial (Fin N) R).coeff (partitionVectorFinsupp nu) ≠ 0
  · obtain ⟨nu, hnu, hmax⟩ := exists_lexKey_max_coeff_ne_zero _ hy
    exact ih nu (hylt nu hnu) y hmax
  · push Not at hy
    have hy0 : y = 0 := Subtype.ext
      (eq_zero_of_isSymmetric_of_coeff_eq_zero ((mem_symmetricSubalgebra _).mp y.2) hy)
    rw [hy0]
    exact Submodule.zero_mem _

/-- A lex-unitriangular family spans the symmetric subalgebra. -/
theorem mem_span_lexUnitriangularFamily (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (x : symmetricSubalgebra (Fin N) R) :
    x ∈ Submodule.span R (Set.range (lexUnitriangularFamily hP)) := by
  by_cases hx : ∃ nu : Nat.PartitionVector N,
      (x : MvPolynomial (Fin N) R).coeff (partitionVectorFinsupp nu) ≠ 0
  · obtain ⟨mu, -, hmax⟩ := exists_lexKey_max_coeff_ne_zero _ hx
    exact mem_span_of_lexKey_le hP mu x hmax
  · push Not at hx
    have hx0 : x = 0 := Subtype.ext
      (eq_zero_of_isSymmetric_of_coeff_eq_zero ((mem_symmetricSubalgebra _).mp x.2) hx)
    rw [hx0]
    exact Submodule.zero_mem _

/-- A lex-unitriangular family is a basis of the symmetric subalgebra. -/
def lexUnitriangularBasis (hP : ∀ lam, IsLexUnitriangular (P lam) lam) :
    Module.Basis (Nat.PartitionVector N) R (symmetricSubalgebra (Fin N) R) :=
  Module.Basis.mk (v := lexUnitriangularFamily hP)
    (by
      rw [linearIndependent_iff]
      intro c hc
      apply (linearIndependent_iff.mp (linearIndependent_of_isLexUnitriangular hP)) c
      have h := congrArg Subtype.val hc
      rw [Finsupp.linearCombination_apply] at h ⊢
      simpa [Finsupp.sum, lexUnitriangularFamily] using h)
    (fun x _ ↦ mem_span_lexUnitriangularFamily hP x)

/-- The basis vectors of `lexUnitriangularBasis` are the members of the family. -/
@[simp]
theorem coe_lexUnitriangularBasis (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (lam : Nat.PartitionVector N) :
    (lexUnitriangularBasis hP lam : MvPolynomial (Fin N) R) = P lam := by
  simp [lexUnitriangularBasis, lexUnitriangularFamily]

end Unitriangular

section Regularity

variable {O K : Type*} [CommRing O] [CommRing K] [Algebra O K]

/-- Lex-unitriangularity can be read off after an injective coefficient map. -/
theorem IsLexUnitriangular.of_map (hinj : Function.Injective (algebraMap O K))
    {q : MvPolynomial (Fin N) O} {lam : Nat.PartitionVector N}
    (h : IsLexUnitriangular (map (algebraMap O K) q) lam) : IsLexUnitriangular q lam where
  isSymmetric e := by
    apply map_injective _ hinj
    rw [map_rename]
    exact h.isSymmetric e
  coeff_self := hinj (by rw [← coeff_map, h.coeff_self, map_one])
  coeff_eq_zero_of_lt mu hmu := hinj (by rw [← coeff_map, h.coeff_eq_zero_of_lt mu hmu, map_zero])

/-- Lex-unitriangularity is preserved by every coefficient map. -/
theorem IsLexUnitriangular.map {F : Type*} [CommRing F] (f : O →+* F)
    {q : MvPolynomial (Fin N) O} {lam : Nat.PartitionVector N}
    (h : IsLexUnitriangular q lam) : IsLexUnitriangular (map f q) lam where
  isSymmetric := h.isSymmetric.map f
  coeff_self := by rw [coeff_map, h.coeff_self, map_one]
  coeff_eq_zero_of_lt mu hmu := by rw [coeff_map, h.coeff_eq_zero_of_lt mu hmu, map_zero]

variable {P : Nat.PartitionVector N → MvPolynomial (Fin N) K}

/-- If the `O`-span of a lex-unitriangular family is stable under multiplication by the
elementary symmetric polynomials, then it contains the image of every symmetric polynomial with
coefficients in `O`. -/
theorem map_mem_span_of_isSymmetric (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hmul : ∀ (r : ℕ) (lam : Nat.PartitionVector N),
      esymm (Fin N) K r * P lam ∈ Submodule.span O (Set.range P))
    {g : MvPolynomial (Fin N) O} (hg : g.IsSymmetric) :
    map (algebraMap O K) g ∈ Submodule.span O (Set.range P) := by
  have hclosed (r : ℕ) {x : MvPolynomial (Fin N) K}
      (hx : x ∈ Submodule.span O (Set.range P)) :
      esymm (Fin N) K r * x ∈ Submodule.span O (Set.range P) := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨lam, rfl⟩ := hx
        exact hmul r lam
    | zero => simp
    | add x y _ _ hx hy =>
        rw [mul_add]
        exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ a hx
  have hone : (1 : MvPolynomial (Fin N) K) ∈ Submodule.span O (Set.range P) := by
    rw [← (hP 0).eq_one]
    exact Submodule.subset_span ⟨0, rfl⟩
  obtain ⟨p, hp⟩ := esymmAlgHom_surjective O (Fintype.card_fin N).le
    (⟨g, (mem_symmetricSubalgebra g).mpr hg⟩ : symmetricSubalgebra (Fin N) O)
  have hgp : g = aeval (fun i : Fin N ↦ esymm (Fin N) O (i + 1)) p := by
    have h := congrArg Subtype.val hp
    rw [esymmAlgHom_apply] at h
    exact h.symm
  rw [hgp]
  clear hgp hp hg
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hC : map (algebraMap O K) (aeval (fun i : Fin N ↦ esymm (Fin N) O (i + 1)) (C a)) =
          a • (1 : MvPolynomial (Fin N) K) := by
        rw [aeval_C, Algebra.smul_def, mul_one, MvPolynomial.algebraMap_apply,
          MvPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_C]
      rw [hC]
      exact Submodule.smul_mem _ a hone
  | add p q hp hq =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hp hq
  | mul_X p i hp =>
      rw [map_mul, aeval_X, map_mul, map_esymm, mul_comm]
      exact hclosed _ hp

/-- **Regularity.**  Let `O → K` be injective.  If the `O`-span of a lex-unitriangular family over
`K` is stable under multiplication by every elementary symmetric polynomial, then every member of
the family has all its coefficients in `O`. -/
theorem mem_range_map_of_isLexUnitriangular (hinj : Function.Injective (algebraMap O K))
    (hP : ∀ lam, IsLexUnitriangular (P lam) lam)
    (hmul : ∀ (r : ℕ) (lam : Nat.PartitionVector N),
      esymm (Fin N) K r * P lam ∈ Submodule.span O (Set.range P))
    (lam : Nat.PartitionVector N) : P lam ∈ Set.range (map (algebraMap O K)) := by
  classical
  induction lam using wellFounded_lexKey.induction with
  | _ lam ih =>
  have hspan := map_mem_span_of_isSymmetric hP hmul (orbitSum_X_isSymmetric O lam)
  rw [map_orbitSum_X, Finsupp.mem_span_range_iff_exists_finsupp] at hspan
  obtain ⟨c, hc⟩ := hspan
  have hle : ∀ eta ∈ c.support, eta ≠ lam → lexKey eta < lexKey lam := by
    by_contra hcon
    push Not at hcon
    obtain ⟨eta, heta, hne, hge⟩ := hcon
    have hlt : lexKey lam < lexKey eta :=
      (not_lt.mp hge).lt_of_ne fun h ↦ hne (lexKey_injective h).symm
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at heta
    obtain ⟨mu, hmu, hmax⟩ := exists_lexKey_max_of_ne_zero hc0
    have hlt' : lexKey lam < lexKey mu := by
      rcases eq_or_ne eta mu with rfl | h
      · exact hlt
      · exact hlt.trans (hmax eta heta h)
    have hmulam : mu ≠ lam := fun h ↦ hlt'.ne (congrArg lexKey h).symm
    have h1 := coeff_sum_smul_of_isLexUnitriangular hP c hmax
    rw [hc, coeff_orbitSum_X] at h1
    simp only [hmulam, ite_false] at h1
    exact Finsupp.mem_support_iff.mp hmu (hinj (by rw [← h1, map_zero]))
  have hcl : c lam = 1 := by
    have h1 := coeff_sum_smul_of_isLexUnitriangular hP c hle
    rw [hc, coeff_orbitSum_X] at h1
    simp only [ite_true] at h1
    exact hinj (by rw [← h1, map_one])
  have hsplit : orbitSum lam X = (c.erase lam).sum (fun eta a ↦ a • P eta) + P lam := by
    rw [← hc]
    conv_lhs => rw [← Finsupp.erase_add_single lam c]
    rw [Finsupp.sum_add_index' (fun eta ↦ zero_smul O (P eta))
        (fun eta a b ↦ add_smul a b (P eta)),
      Finsupp.sum_single_index (zero_smul O (P lam)), hcl, one_smul]
  have hsmul (a : O) {x : MvPolynomial (Fin N) K} (hx : x ∈ (map (algebraMap O K)).range) :
      a • x ∈ (map (algebraMap O K)).range := by
    obtain ⟨y, rfl⟩ := hx
    refine ⟨C a * y, ?_⟩
    rw [map_mul, map_C, Algebra.smul_def, MvPolynomial.algebraMap_apply]
  have hsum : (c.erase lam).sum (fun eta a ↦ a • P eta) ∈ (map (algebraMap O K)).range := by
    refine Subring.sum_mem _ fun eta heta ↦ hsmul _ ?_
    rw [Finsupp.support_erase, Finset.mem_erase] at heta
    obtain ⟨y, hy⟩ := ih eta (hle eta heta.2 heta.1)
    exact ⟨y, hy⟩
  have horbit : orbitSum lam X ∈ (map (algebraMap O K)).range :=
    ⟨orbitSum lam X, map_orbitSum_X O _ lam⟩
  have hP' : P lam = orbitSum lam X - (c.erase lam).sum (fun eta a ↦ a • P eta) := by
    rw [hsplit, add_sub_cancel_left]
  obtain ⟨y, hy⟩ := Subring.sub_mem _ horbit hsum
  exact ⟨y, hy.trans hP'.symm⟩

end Regularity

end PartitionDivision.Macdonald
