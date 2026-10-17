/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Order.Minimal

/-!
# Abstract evaluation symmetry and normalized Pieri

This file isolates the simultaneous induction in Macdonald, Chapter VI, (6.6)--(6.8).
It assumes the grid recurrence and the two finite-dimensional consequences of
unitriangularity: a lower-ideal expansion and separation by the lower evaluation matrix.
No difference operator is part of the statement.

The relation `r nu mu` means that `nu` occurs earlier than `mu` in the induction.  In the
Macdonald application it is the lexicographic order within a fixed size, preceded by size.
The finite set `lower mu` is the non-strict principal ideal: it contains `mu` itself.

## Concrete partition-vector instance

Every structural hypothesis below has the following intended instance for
`I = Nat.PartitionVector N`.

* `base = 0`, and `r` compares size first and lexicographic order second.
* For nonzero `top`, let `step top` be its number of positive parts and let `parent top` be
  `top - 1 ^ (step top)`, coordinatewise.  Its size is smaller by `step top`, adding the
  corresponding prefix strip recovers `top`, and this strip is legal.
* `lowerTop top` consists of the vectors of size `|top|` that are lexicographically at most
  `top`.  Any legal `step top`-strip added to `parent top` lies in this set: the prefix strip is
  lexicographically greatest.
* For an arbitrary pair `mu, s`, take `lowerPS mu s` to be the vectors of size `|mu| + s`
  lexicographically at most `mu + 1 ^ s`.  It contains every legal `s`-strip successor.
* `next` is the finite set of legal `Fin N → Fin 2` strips of cardinality `s`.  The definitions
  `Strip`, `IsLegal`, and `prefixOnes` are already in
  `PartitionDivision.Macdonald.PieriCoefficient`.

Thus the chosen `parent` and `step` are used only to prove symmetry.  Arbitrary Pieri pairs use
their own `lowerPS`; no surjectivity or coverage property of the chosen decomposition is needed.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Macdonald

variable {K A I S : Type*} [Field K] [CommRing A] [Algebra K A]

/-- Data used by the abstract form of Macdonald's simultaneous symmetry--Pieri induction. -/
structure EvaluationPieriData where
  /-- Evaluation at a grid indexed by `I`. -/
  eval : I → A →ₐ[K] K
  /-- The normalized triangular family. -/
  p : I → A
  /-- The elementary multiplier associated with a step. -/
  elem : S → A
  /-- Legal successors of an index for a step. -/
  next : I → S → Finset I
  /-- Coefficient of a legal successor in the grid recurrence. -/
  coeff : I → S → I → K

namespace EvaluationPieriData

variable (D : EvaluationPieriData (K := K) (A := A) (I := I) (S := S))

/-- Divide a family member by its value at the base grid. -/
def normalizeAt (base : I) (mu : I) : A :=
  (D.eval base (D.p mu))⁻¹ • D.p mu

/-- Replace the family in evaluation--Pieri data by its base-grid normalization. -/
def normalized (base : I) : EvaluationPieriData (K := K) (A := A) (I := I) (S := S) :=
  { D with p := D.normalizeAt base }

/-- A normalized family member evaluates to one at the base grid when its denominator is
nonzero. -/
@[simp]
theorem eval_normalizeAt_eq_one (base mu : I) (hne : D.eval base (D.p mu) ≠ 0) :
    D.eval base (D.normalizeAt base mu) = 1 := by
  simp [normalizeAt, hne]

/-- Evaluation symmetry for one index against every other index. -/
def SymmetricAt (mu : I) : Prop :=
  ∀ lam, D.eval lam (D.p mu) = D.eval mu (D.p lam)

/-- The normalized Pieri identity at an index and a step. -/
def PieriAt (mu : I) (s : S) : Prop :=
  D.p mu * D.elem s =
    ∑ nu ∈ D.next mu s, D.coeff mu s nu • D.p nu

/-- The grid recurrence, in the normalization used by the simultaneous induction. -/
def HasGridRecurrence : Prop :=
  ∀ lam mu s,
    D.eval lam (D.elem s) * D.eval mu (D.p lam) =
      ∑ nu ∈ D.next mu s, D.coeff mu s nu * D.eval nu (D.p lam)

/-- The grid recurrence is unchanged when every family member is divided by its value at the
base grid. -/
theorem HasGridRecurrence.normalized (hrec : D.HasGridRecurrence) (base : I) :
    (D.normalized base).HasGridRecurrence := by
  intro lam mu s
  change D.eval lam (D.elem s) *
      D.eval mu ((D.eval base (D.p lam))⁻¹ • D.p lam) =
    ∑ nu ∈ D.next mu s,
      D.coeff mu s nu * D.eval nu ((D.eval base (D.p lam))⁻¹ • D.p lam)
  simp_rw [map_smul, smul_eq_mul]
  calc
    D.eval lam (D.elem s) *
        ((D.eval base (D.p lam))⁻¹ * D.eval mu (D.p lam)) =
        (D.eval base (D.p lam))⁻¹ *
          (D.eval lam (D.elem s) * D.eval mu (D.p lam)) := by
      ac_rfl
    _ = (D.eval base (D.p lam))⁻¹ *
        ∑ nu ∈ D.next mu s,
          D.coeff mu s nu * D.eval nu (D.p lam) := by
      rw [hrec lam mu s]
    _ = ∑ nu ∈ D.next mu s,
        (D.eval base (D.p lam))⁻¹ *
          (D.coeff mu s nu * D.eval nu (D.p lam)) := by
      rw [Finset.mul_sum]
    _ = ∑ nu ∈ D.next mu s,
        D.coeff mu s nu *
          ((D.eval base (D.p lam))⁻¹ * D.eval nu (D.p lam)) := by
      apply Finset.sum_congr rfl
      intro nu hnu
      ac_rfl

/-- A finite evaluation matrix separates coefficient vectors supported on `lower`. -/
def SeparatesOn (lower : Finset I) : Prop :=
  ∀ a b : I → K,
    (∀ pi ∈ lower,
      (∑ nu ∈ lower, a nu * D.eval pi (D.p nu)) =
        ∑ nu ∈ lower, b nu * D.eval pi (D.p nu)) →
      ∀ nu ∈ lower, a nu = b nu

/-- Membership in the span of family members indexed by a finite set. -/
def InSpanOn (lower : Finset I) (x : A) : Prop :=
  x ∈ Submodule.span K (D.p '' (lower : Set I))

/-- The one-step heart of Macdonald VI (6.6)--(6.8).

The hypotheses say that `p parent * elem step` has an expansion on the non-strict lower ideal
of `top`, that the evaluation matrix on this ideal is nonsingular, and that symmetry is already
known at every strict lower index.  The conclusions are the Pieri identity for `parent` and
evaluation symmetry at `top`. -/
theorem pieriAt_and_symmetricAt_of_lower
    (hrec : D.HasGridRecurrence) (lower : Finset I) (top parent : I) (step : S)
    (htop : top ∈ D.next parent step) (hnext : D.next parent step ⊆ lower)
    (hparentSymm : D.SymmetricAt parent) (hne : D.coeff parent step top ≠ 0)
    (hknown : ∀ nu ∈ lower, nu ≠ top → D.SymmetricAt nu)
    (hsep : D.SeparatesOn lower)
    (hexpand : D.InSpanOn lower (D.p parent * D.elem step)) :
    D.PieriAt parent step ∧ D.SymmetricAt top := by
  classical
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_span_image_finset_iff_exists_fun' K).mp hexpand
  have ha := ha.symm
  let b : I → K := fun nu ↦ if nu ∈ D.next parent step then D.coeff parent step nu else 0
  have hcoeff : ∀ nu ∈ lower, a nu = b nu := by
    apply hsep a b
    intro pi hpi
    have hevalExpansion := congrArg (D.eval pi) ha
    simp only [map_mul, map_sum, Algebra.smul_def, AlgHom.commutes,
      Algebra.algebraMap_self_apply] at hevalExpansion
    rw [← hevalExpansion, mul_comm]
    rw [hparentSymm pi]
    rw [hrec pi parent step]
    have hsymm (nu : I) (hnu : nu ∈ D.next parent step) :
        D.eval nu (D.p pi) = D.eval pi (D.p nu) := by
      by_cases hnutop : nu = top
      · subst nu
        by_cases hpitop : pi = top
        · subst pi
          rfl
        · exact hknown pi hpi hpitop top
      · exact (hknown nu (hnext hnu) hnutop pi).symm
    calc
      (∑ nu ∈ D.next parent step,
          D.coeff parent step nu * D.eval nu (D.p pi)) =
          ∑ nu ∈ D.next parent step,
            D.coeff parent step nu * D.eval pi (D.p nu) := by
        apply Finset.sum_congr rfl
        intro nu hnu
        rw [hsymm nu hnu]
      _ = ∑ nu ∈ D.next parent step, b nu * D.eval pi (D.p nu) := by
        apply Finset.sum_congr rfl
        intro nu hnu
        have hb : b nu = D.coeff parent step nu := by simp [b, hnu]
        rw [hb]
      _ = ∑ nu ∈ lower, b nu * D.eval pi (D.p nu) := by
        apply Finset.sum_subset hnext
        intro nu hnuLower hnuNext
        have hb : b nu = 0 := by simp [b, hnuNext]
        rw [hb, zero_mul]
  have hpieri : D.PieriAt parent step := by
    rw [PieriAt, ha]
    calc
      (∑ nu ∈ lower, a nu • D.p nu) =
          ∑ nu ∈ lower, b nu • D.p nu := by
        apply Finset.sum_congr rfl
        intro nu hnu
        rw [hcoeff nu hnu]
      _ = ∑ nu ∈ D.next parent step, D.coeff parent step nu • D.p nu := by
        calc
          (∑ nu ∈ lower, b nu • D.p nu) =
              ∑ nu ∈ D.next parent step, b nu • D.p nu := by
            symm
            apply Finset.sum_subset hnext
            intro nu hnuLower hnuNext
            simp [b, hnuNext]
          _ = ∑ nu ∈ D.next parent step,
              D.coeff parent step nu • D.p nu := by
            apply Finset.sum_congr rfl
            intro nu hnu
            simp [b, hnu]
  refine ⟨hpieri, ?_⟩
  intro lam
  have hevalPieri := congrArg (D.eval lam) hpieri
  simp only [map_mul, map_sum, Algebra.smul_def, AlgHom.commutes,
    Algebra.algebraMap_self_apply] at hevalPieri
  rw [hparentSymm lam] at hevalPieri
  have hrecurrence := hrec lam parent step
  have hlowerTerms :
      ∑ nu ∈ D.next parent step \ {top},
          D.coeff parent step nu * D.eval lam (D.p nu) =
        ∑ nu ∈ D.next parent step \ {top},
          D.coeff parent step nu * D.eval nu (D.p lam) := by
    apply Finset.sum_congr rfl
    intro nu hnu
    have hnuNext : nu ∈ D.next parent step := (Finset.mem_sdiff.mp hnu).1
    have hnuTop : nu ≠ top := by simpa using (Finset.mem_sdiff.mp hnu).2
    rw [hknown nu (hnext hnuNext) hnuTop lam]
  rw [← Finset.sum_erase_add _ _ htop] at hevalPieri
  rw [← Finset.sum_erase_add _ _ htop] at hrecurrence
  simp only [Finset.erase_eq] at hevalPieri hrecurrence
  rw [hlowerTerms] at hevalPieri
  have hmul :
      D.coeff parent step top * D.eval lam (D.p top) =
        D.coeff parent step top * D.eval top (D.p lam) := by
    have hleft :
        D.eval parent (D.p lam) * D.eval lam (D.elem step) =
          D.eval lam (D.elem step) * D.eval parent (D.p lam) := by
      rw [mul_comm]
    rw [hleft] at hevalPieri
    exact add_left_cancel (hevalPieri.symm.trans hrecurrence)
  exact mul_left_cancel₀ hne hmul

/-- Deduce a Pieri identity for an arbitrary index and step from global evaluation symmetry.

The product is only assumed to belong to the span of the indicated finite family.  Evaluating
an expansion on `lower`, using symmetry and the grid recurrence, and applying separation
identifies every coefficient. -/
theorem pieriAt_of_symmetric
    (hrec : D.HasGridRecurrence) (hsymm : ∀ nu, D.SymmetricAt nu)
    (lower : Finset I) (mu : I) (step : S) (hnext : D.next mu step ⊆ lower)
    (hsep : D.SeparatesOn lower)
    (hexpand : D.InSpanOn lower (D.p mu * D.elem step)) :
    D.PieriAt mu step := by
  classical
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_span_image_finset_iff_exists_fun' K).mp hexpand
  have ha := ha.symm
  let b : I → K := fun nu ↦ if nu ∈ D.next mu step then D.coeff mu step nu else 0
  have hcoeff : ∀ nu ∈ lower, a nu = b nu := by
    apply hsep a b
    intro pi hpi
    have hevalExpansion := congrArg (D.eval pi) ha
    simp only [map_mul, map_sum, Algebra.smul_def, AlgHom.commutes,
      Algebra.algebraMap_self_apply] at hevalExpansion
    rw [← hevalExpansion, mul_comm, hsymm mu pi, hrec pi mu step]
    calc
      (∑ nu ∈ D.next mu step, D.coeff mu step nu * D.eval nu (D.p pi)) =
          ∑ nu ∈ D.next mu step,
            D.coeff mu step nu * D.eval pi (D.p nu) := by
        apply Finset.sum_congr rfl
        intro nu hnu
        rw [← hsymm nu pi]
      _ = ∑ nu ∈ D.next mu step, b nu * D.eval pi (D.p nu) := by
        apply Finset.sum_congr rfl
        intro nu hnu
        have hb : b nu = D.coeff mu step nu := by simp [b, hnu]
        rw [hb]
      _ = ∑ nu ∈ lower, b nu * D.eval pi (D.p nu) := by
        apply Finset.sum_subset hnext
        intro nu hnuLower hnuNext
        have hb : b nu = 0 := by simp [b, hnuNext]
        rw [hb, zero_mul]
  rw [PieriAt, ha]
  calc
    (∑ nu ∈ lower, a nu • D.p nu) =
        ∑ nu ∈ lower, b nu • D.p nu := by
      apply Finset.sum_congr rfl
      intro nu hnu
      rw [hcoeff nu hnu]
    _ = ∑ nu ∈ D.next mu step, b nu • D.p nu := by
      symm
      apply Finset.sum_subset hnext
      intro nu hnuLower hnuNext
      simp [b, hnuNext]
    _ = ∑ nu ∈ D.next mu step, D.coeff mu step nu • D.p nu := by
      apply Finset.sum_congr rfl
      intro nu hnu
      simp [b, hnu]

/-- Prove evaluation symmetry by induction over the chosen initial-column decomposition.

Only the single pair `parent top, step top` chosen for each non-base `top` enters this induction;
no coverage claim for arbitrary pairs is required. -/
theorem symmetricAt_of_induction
    (D : EvaluationPieriData (K := K) (A := A) (I := I) (S := S))
    (r : I → I → Prop) (hwell : WellFounded r) (base : I)
    (lower : I → Finset I) (parent : I → I) (step : I → S)
    (hbase : D.SymmetricAt base) (hrec : D.HasGridRecurrence)
    (hlower : ∀ {nu mu}, nu ∈ lower mu → nu = mu ∨ r nu mu)
    (hparent : ∀ mu, mu ≠ base → r (parent mu) mu)
    (htop : ∀ mu, mu ≠ base → mu ∈ D.next (parent mu) (step mu))
    (hnext : ∀ mu, mu ≠ base → D.next (parent mu) (step mu) ⊆ lower mu)
    (hne : ∀ mu, mu ≠ base → D.coeff (parent mu) (step mu) mu ≠ 0)
    (hsep : ∀ mu, mu ≠ base → D.SeparatesOn (lower mu))
    (hexpand : ∀ mu, mu ≠ base →
      D.InSpanOn (lower mu) (D.p (parent mu) * D.elem (step mu))) :
    ∀ mu, D.SymmetricAt mu := by
  intro mu
  induction mu using hwell.induction with
  | h mu ih =>
    by_cases hmubase : mu = base
    · subst mu
      exact hbase
    · have hparentRel := hparent mu hmubase
      have hparentSymm : D.SymmetricAt (parent mu) := ih (parent mu) hparentRel
      have hknown : ∀ nu ∈ lower mu, nu ≠ mu → D.SymmetricAt nu := by
        intro nu hnu hnumu
        exact ih nu (hlower hnu |>.resolve_left hnumu)
      exact (D.pieriAt_and_symmetricAt_of_lower hrec (lower mu) mu (parent mu)
        (step mu) (htop mu hmubase) (hnext mu hmubase) hparentSymm (hne mu hmubase)
        hknown (hsep mu hmubase) (hexpand mu hmubase)).2

/-- Evaluation symmetry and normalized Pieri for a raw triangular family.

This is the hypothesis-facing form of Macdonald VI (6.6)--(6.8).  The raw grid recurrence is
normalized internally.  `hexpand` is the lower expansion supplied by unitriangularity, while
`hsep` is the nonsingularity of the normalized lower evaluation matrix (equivalently, the
monomial evaluation matrix after unitriangular column operations). -/
theorem normalized_symmetry_and_pieri
    (D : EvaluationPieriData (K := K) (A := A) (I := I) (S := S))
    (r : I → I → Prop) (hwell : WellFounded r) (base : I)
    (lowerTop : I → Finset I) (parent : I → I) (step : I → S)
    (lowerPS : I → S → Finset I)
    (hpbase : D.p base = 1) (hnonzero : ∀ mu, D.eval base (D.p mu) ≠ 0)
    (hrec : D.HasGridRecurrence)
    (hlowerTop : ∀ {nu mu}, nu ∈ lowerTop mu → nu = mu ∨ r nu mu)
    (hparent : ∀ mu, mu ≠ base → r (parent mu) mu)
    (htop : ∀ mu, mu ≠ base → mu ∈ D.next (parent mu) (step mu))
    (hnextTop : ∀ mu, mu ≠ base →
      D.next (parent mu) (step mu) ⊆ lowerTop mu)
    (hne : ∀ mu, mu ≠ base → D.coeff (parent mu) (step mu) mu ≠ 0)
    (hsepTop : ∀ mu, mu ≠ base →
      (D.normalized base).SeparatesOn (lowerTop mu))
    (hexpandTop : ∀ mu, mu ≠ base →
      (D.normalized base).InSpanOn (lowerTop mu)
        (D.normalizeAt base (parent mu) * D.elem (step mu)))
    (hnextPS : ∀ mu s, D.next mu s ⊆ lowerPS mu s)
    (hsepPS : ∀ mu s, (D.normalized base).SeparatesOn (lowerPS mu s))
    (hexpandPS : ∀ mu s, (D.normalized base).InSpanOn (lowerPS mu s)
      (D.normalizeAt base mu * D.elem s)) :
    (∀ mu, D.eval base (D.normalizeAt base mu) = 1) ∧
      (∀ lam mu,
        D.eval lam (D.normalizeAt base mu) = D.eval mu (D.normalizeAt base lam)) ∧
      ∀ mu s, D.normalizeAt base mu * D.elem s =
        ∑ nu ∈ D.next mu s, D.coeff mu s nu • D.normalizeAt base nu := by
  have hbase : (D.normalized base).SymmetricAt base := by
    intro lam
    change D.eval lam (D.normalizeAt base base) = D.eval base (D.normalizeAt base lam)
    rw [D.eval_normalizeAt_eq_one base lam (hnonzero lam)]
    simp [normalizeAt, hpbase]
  have hrecNormalized := HasGridRecurrence.normalized D hrec base
  have hsymm := (D.normalized base).symmetricAt_of_induction r hwell base lowerTop
    parent step hbase hrecNormalized hlowerTop hparent htop hnextTop hne hsepTop
    hexpandTop
  refine ⟨fun mu ↦ D.eval_normalizeAt_eq_one base mu (hnonzero mu), ?_, ?_⟩
  · exact fun lam mu ↦ hsymm mu lam
  · intro mu s
    exact (D.normalized base).pieriAt_of_symmetric hrecNormalized hsymm
      (lowerPS mu s) mu s (hnextPS mu s) (hsepPS mu s) (hexpandPS mu s)

end EvaluationPieriData

end Macdonald
