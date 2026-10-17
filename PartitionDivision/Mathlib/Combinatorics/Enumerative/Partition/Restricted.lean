/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Fin.Tuple.Finset
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Partitions with bounded consecutive differences

This file models a partition with at most `N` parts as an antitone function
`Fin N → ℕ`, padded by zeros after its last coordinate.  This representation is preferable here
to `Nat.Partition`: it retains a fixed number of coordinates, so consecutive differences give a
literal equivalence with `Fin N → ℕ`.  It also avoids choosing an ambient total size, which
would be necessary for `Nat.Partition`.

The main results are:

* `Nat.PartitionVector.differencesEquiv`, the equivalence between weakly decreasing vectors and
  their consecutive differences;
* `Nat.PartitionVector.decompositionEquiv`, Euclidean division of all differences by `k`;
* `Nat.PartitionVector.card_kRestricted`, the count `k ^ N`.

A bridge to `Nat.Partition` is not included.  For fixed `n`, its exact statement would be an
equivalence between `{p : Nat.Partition n // p.parts.card ≤ N}` and
`{v : PartitionVector N // ∑ i, v i = n}`.  Constructing its inverse requires the missing API
that sorts the multiset of parts, pads it to `Fin N`, and proves that deleting the zeros recovers
the original multiset.  None of those facts is needed below.
-/

@[expose] public section

open Function

namespace Nat

/-- A weakly decreasing vector of `N` natural numbers, regarded as a partition with at most `N`
parts. -/
def PartitionVector (N : ℕ) := { p : Fin N → ℕ // Antitone p }

namespace PartitionVector

variable {N k : ℕ}

/-- A partition vector is coerced to its function of parts. -/
instance : CoeFun (PartitionVector N) fun _ ↦ Fin N → ℕ := ⟨Subtype.val⟩

/-- Two partition vectors are equal when all their parts are equal. -/
@[ext]
theorem ext {p q : PartitionVector N} (h : ∀ i, p i = q i) : p = q := by
  exact Subtype.ext (funext h)

/-- The parts of a partition vector are weakly decreasing. -/
theorem antitone (p : PartitionVector N) : Antitone p := p.2

/-- Partition vectors have decidable equality. -/
instance : DecidableEq (PartitionVector N) := Subtype.instDecidableEq

/-- The empty partition vector. -/
instance : Zero (PartitionVector N) := ⟨⟨0, antitone_const⟩⟩

/-- Evaluation of the empty partition vector. -/
@[simp]
theorem zero_apply (i : Fin N) : (0 : PartitionVector N) i = 0 := rfl

/-- The pointwise sum of two partition vectors. -/
instance : Add (PartitionVector N) where
  add p q := ⟨p + q, p.2.add q.2⟩

/-- Addition of partition vectors is pointwise addition. -/
@[simp]
theorem add_apply (p q : PartitionVector N) (i : Fin N) : (p + q) i = p i + q i := rfl

/-- Natural scalar multiplication of partition vectors. -/
instance : SMul ℕ (PartitionVector N) where
  smul a p := ⟨a • (p : Fin N → ℕ), fun _ _ h ↦ Nat.mul_le_mul_left a (p.2 h)⟩

/-- Scalar multiplication of partition vectors is pointwise multiplication. -/
@[simp]
theorem smul_apply (a : ℕ) (p : PartitionVector N) (i : Fin N) :
    (a • p) i = a * p i := rfl

/-- Remove the last part of a partition vector and subtract that last part from every remaining
part.  The inverse appends the removed part after adding it back to the prefix. -/
def snocEquiv (N : ℕ) : PartitionVector (N + 1) ≃ ℕ × PartitionVector N where
  toFun p :=
    (p (Fin.last N),
      ⟨fun i ↦ p i.castSucc - p (Fin.last N), fun i j hij ↦ by
        exact Nat.sub_le_sub_right (p.2 (Fin.castSucc_le_castSucc_iff.mpr hij)) _⟩)
  invFun p :=
    ⟨Fin.snoc (fun i ↦ p.2 i + p.1) p.1, fun i j hij ↦ by
      cases j using Fin.lastCases with
      | last =>
          cases i using Fin.lastCases <;> simp
      | cast j =>
          cases i using Fin.lastCases with
          | last => simp at hij
          | cast i =>
              simpa only [Fin.snoc_castSucc] using
                Nat.add_le_add_right (p.2.2 (by simpa using hij)) p.1⟩
  left_inv p := by
    apply ext
    intro i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simp
    · simp only [Fin.snoc_castSucc]
      exact Nat.sub_add_cancel (p.2 (Fin.le_last i.castSucc))
  right_inv p := by
    apply Prod.ext
    · simp
    · apply ext
      intro i
      simp

/-- The first component of `snocEquiv` is the last part. -/
@[simp]
theorem snocEquiv_fst (p : PartitionVector (N + 1)) :
    (snocEquiv N p).1 = p (Fin.last N) := rfl

/-- The second component of `snocEquiv` is the prefix after subtracting the last part. -/
@[simp]
theorem snocEquiv_snd_apply (p : PartitionVector (N + 1)) (i : Fin N) :
    (snocEquiv N p).2 i = p i.castSucc - p (Fin.last N) := rfl

/-- Extending the normalized prefix by zero agrees with extending the original vector and then
subtracting its last part. -/
theorem lastCases_snocEquiv_snd (p : PartitionVector (N + 1)) (i : Fin (N + 1)) :
    Fin.lastCases 0 (snocEquiv N p).2 i =
      Fin.lastCases 0 p i.castSucc - p (Fin.last N) := by
  cases i using Fin.lastCases <;> simp

/-- Consecutive differences give an equivalence from weakly decreasing vectors to arbitrary
vectors of natural numbers.  The inverse takes suffix sums. -/
def differencesEquiv : ∀ N : ℕ, PartitionVector N ≃ (Fin N → ℕ)
  | 0 =>
      { toFun := fun _ i ↦ Fin.elim0 i
        invFun := fun _ ↦ 0
        left_inv := fun _ ↦ ext fun i ↦ Fin.elim0 i
        right_inv := fun _ ↦ funext fun i ↦ Fin.elim0 i }
  | N + 1 =>
      (snocEquiv N).trans <|
        ((Equiv.refl ℕ).prodCongr (differencesEquiv N)).trans (Fin.snocEquiv (fun _ ↦ ℕ))

/-- The part after `i`, with the value after the final coordinate defined to be zero. -/
def nextPart (p : PartitionVector N) (i : Fin N) : ℕ :=
  Fin.lastCases 0 p i.succ

/-- The consecutive difference at `i`, including the final difference from the last part to
zero. -/
def difference (p : PartitionVector N) (i : Fin N) : ℕ := p i - p.nextPart i

/-- The part after the final coordinate is zero. -/
@[simp]
theorem nextPart_last (p : PartitionVector (N + 1)) : p.nextPart (Fin.last N) = 0 := by
  simp [nextPart, Fin.succ_last]

/-- Away from the final coordinate, `nextPart` is evaluation at the successor. -/
@[simp]
theorem nextPart_castSucc (p : PartitionVector (N + 1)) (i : Fin N) :
    p.nextPart i.castSucc = p i.succ := by
  simp [nextPart, ← Fin.castSucc_succ]

/-- The next part never exceeds the current part. -/
theorem nextPart_le (p : PartitionVector N) (i : Fin N) : p.nextPart i ≤ p i := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ N =>
      cases i using Fin.lastCases with
      | last => simp
      | cast i => simpa using p.2 (Fin.castSucc_le_succ i)

/-- Taking the next part commutes with addition. -/
@[simp]
theorem nextPart_add (p q : PartitionVector N) (i : Fin N) :
    (p + q).nextPart i = p.nextPart i + q.nextPart i := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ N =>
      cases i using Fin.lastCases <;> simp

/-- Taking the next part commutes with natural scalar multiplication. -/
@[simp]
theorem nextPart_smul (a : ℕ) (p : PartitionVector N) (i : Fin N) :
    (a • p).nextPart i = a * p.nextPart i := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ N =>
      cases i using Fin.lastCases <;> simp

/-- Consecutive differences commute with addition of partition vectors. -/
@[simp]
theorem difference_add (p q : PartitionVector N) (i : Fin N) :
    (p + q).difference i = p.difference i + q.difference i := by
  have hp := p.nextPart_le i
  have hq := q.nextPart_le i
  simp only [difference, add_apply, nextPart_add]
  lia

/-- Consecutive differences commute with natural scalar multiplication. -/
@[simp]
theorem difference_smul (a : ℕ) (p : PartitionVector N) (i : Fin N) :
    (a • p).difference i = a * p.difference i := by
  simp [difference, Nat.mul_sub_left_distrib]

/-- The recursive difference equivalence really records the consecutive differences. -/
theorem differencesEquiv_apply (N : ℕ) (p : PartitionVector N) (i : Fin N) :
    differencesEquiv N p i = p.difference i := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ N ih =>
      cases i using Fin.lastCases with
      | last =>
          simp [differencesEquiv, snocEquiv, difference, nextPart, Fin.succ_last]
          rfl
      | cast i =>
          simp only [differencesEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
            Fin.snocEquiv_apply, Fin.snoc_castSucc]
          change differencesEquiv N (snocEquiv N p).2 i = _
          rw [ih]
          simp only [difference, nextPart, snocEquiv_snd_apply]
          rw [lastCases_snocEquiv_snd, Fin.castSucc_succ]
          rw [tsub_tsub_tsub_cancel_right]
          simpa only [← Fin.castSucc_succ, Fin.lastCases_castSucc] using
            p.2 (Fin.le_last i.succ)

private theorem difference_snocEquiv_snd (p : PartitionVector (N + 1)) (i : Fin N) :
    (snocEquiv N p).2.difference i = p.difference i.castSucc := by
  rw [← differencesEquiv_apply, ← differencesEquiv_apply]
  simp only [differencesEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Fin.snocEquiv_apply, Fin.snoc_castSucc]
  rfl

private theorem sum_Ici_castSucc (f : Fin (N + 1) → ℕ) (i : Fin N) :
    (∑ j ∈ Finset.Ici i.castSucc, f j) =
      (∑ j ∈ Finset.Ici i, f j.castSucc) + f (Fin.last N) := by
  calc
    (∑ j ∈ Finset.Ici i.castSucc, f j) =
        ∑ j : Fin (N + 1), if i.castSucc ≤ j then f j else 0 := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      apply Finset.sum_congr
      · ext j
        simp
      · simp
    _ = (∑ j : Fin N, if i.castSucc ≤ j.castSucc then f j.castSucc else 0) +
        (if i.castSucc ≤ Fin.last N then f (Fin.last N) else 0) :=
      Fin.sum_univ_castSucc _
    _ = (∑ j ∈ Finset.Ici i, f j.castSucc) + f (Fin.last N) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      simp only [ite_eq_left (Fin.le_last i.castSucc)]
      congr 1
      apply Finset.sum_congr
      · ext j
        simp
      · simp

/-- Every part is the suffix sum of the consecutive differences beginning at that coordinate. -/
theorem apply_eq_sum_Ici_difference (p : PartitionVector N) (i : Fin N) :
    p i = ∑ j ∈ Finset.Ici i, p.difference j := by
  induction N with
  | zero => exact Fin.elim0 i
  | succ N ih =>
      cases i using Fin.lastCases with
      | last =>
          rw [show Finset.Ici (Fin.last N) = {Fin.last N} by ext; simp]
          simp [difference]
      | cast i =>
          let q := (snocEquiv N p).2
          calc
            p i.castSucc = q i + p (Fin.last N) := by
              exact (Nat.sub_add_cancel (p.2 (Fin.le_last i.castSucc))).symm
            _ = (∑ j ∈ Finset.Ici i, q.difference j) + p (Fin.last N) := by
              rw [← ih q i]
            _ = (∑ j ∈ Finset.Ici i, p.difference j.castSucc) + p (Fin.last N) := by
              congr 1
              apply Finset.sum_congr rfl
              intro j _
              exact difference_snocEquiv_snd p j
            _ = ∑ j ∈ Finset.Ici i.castSucc, p.difference j := by
              rw [sum_Ici_castSucc]
              congr 1
              simp [difference]

/-- The inverse of `differencesEquiv` is given by suffix sums. -/
theorem differencesEquiv_symm_apply (d : Fin N → ℕ) (i : Fin N) :
    (differencesEquiv N).symm d i = ∑ j ∈ Finset.Ici i, d j := by
  rw [apply_eq_sum_Ici_difference]
  apply Finset.sum_congr rfl
  intro j _
  rw [← differencesEquiv_apply]
  simp

/-- A partition vector is `k`-restricted when every consecutive difference, including the final
difference to zero, is less than `k`. -/
def IsKRestricted (k : ℕ) (p : PartitionVector N) : Prop := ∀ i, p.difference i < k

/-- The type of `k`-restricted partition vectors with `N` parts. -/
def KRestricted (N k : ℕ) := { p : PartitionVector N // p.IsKRestricted k }

/-- `k`-restricted partition vectors have decidable equality. -/
instance : DecidableEq (KRestricted N k) := Subtype.instDecidableEq

/-- The equivalence between `k`-restricted partition vectors and vectors with entries in `Fin k`.
-/
def kRestrictedEquiv (N k : ℕ) : KRestricted N k ≃ (Fin N → Fin k) where
  toFun p i := ⟨differencesEquiv N p.1 i, by
    rw [differencesEquiv_apply]
    exact p.2 i⟩
  invFun d :=
    ⟨(differencesEquiv N).symm (fun i ↦ d i), fun i ↦ by
      rw [← differencesEquiv_apply]
      simp⟩
  left_inv p := by
    apply Subtype.ext
    apply (differencesEquiv N).injective
    ext i
    simp
  right_inv d := by
    ext i
    simp

/-- Applying `differencesEquiv` after decoding a restricted difference vector recovers that
vector. -/
@[simp]
theorem differencesEquiv_kRestrictedEquiv_symm_apply (d : Fin N → Fin k) (i : Fin N) :
    differencesEquiv N ((kRestrictedEquiv N k).symm d).1 i = d i := by
  change differencesEquiv N ((differencesEquiv N).symm (fun i ↦ d i)) i = d i
  simp

/-- The finite type structure on `k`-restricted partition vectors induced by their difference
vectors. -/
instance : Fintype (KRestricted N k) :=
  Fintype.ofEquiv (Fin N → Fin k) (kRestrictedEquiv N k).symm

/-- The finset of all `k`-restricted partition vectors, viewed as ordinary partition vectors. -/
def kRestrictedFinset (N k : ℕ) : Finset (PartitionVector N) :=
  Finset.univ.map
    { toFun := fun p : KRestricted N k ↦ p.1
      inj' := fun _ _ h ↦ Subtype.ext h }

/-- Membership in `kRestrictedFinset` is equivalent to having all differences less than `k`. -/
@[simp]
theorem mem_kRestrictedFinset (p : PartitionVector N) :
    p ∈ kRestrictedFinset N k ↔ p.IsKRestricted k := by
  constructor
  · rw [kRestrictedFinset, Finset.mem_map]
    rintro ⟨q, _, rfl⟩
    exact q.2
  · intro hp
    rw [kRestrictedFinset, Finset.mem_map]
    exact ⟨⟨p, hp⟩, Finset.mem_univ _, rfl⟩

/-- There are `k ^ N` many `k`-restricted partition vectors with `N` parts. -/
theorem card_kRestricted (N k : ℕ) : Fintype.card (KRestricted N k) = k ^ N := by
  calc
    Fintype.card (KRestricted N k) = Fintype.card (Fin N → Fin k) :=
      Fintype.card_congr (kRestrictedEquiv N k)
    _ = k ^ N := by simp

/-- The finset of `k`-restricted partition vectors has cardinality `k ^ N`. -/
@[simp]
theorem card_kRestrictedFinset (N k : ℕ) : (kRestrictedFinset N k).card = k ^ N := by
  rw [kRestrictedFinset, Finset.card_map, Finset.card_univ, card_kRestricted]

/-- Coordinatewise Euclidean division, arranged with the remainders before the quotients. -/
def divisionCoordinatesEquiv (N k : ℕ) [NeZero k] :
    (Fin N → ℕ) ≃ (Fin N → Fin k) × (Fin N → ℕ) :=
  (Equiv.piCongrRight fun _ ↦ Nat.divModEquiv k).trans <|
    (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ ↦ ℕ) (fun _ ↦ Fin k)).trans <|
      Equiv.prodComm _ _

/-- Every partition vector is equivalent to a pair consisting of a `k`-restricted partition
vector and an arbitrary partition vector.  The differences of the two outputs are respectively
the remainders and quotients on division by `k`. -/
def decompositionEquiv (N k : ℕ) (hk : 0 < k) :
    PartitionVector N ≃ KRestricted N k × PartitionVector N := by
  letI : NeZero k := ⟨hk.ne'⟩
  exact (differencesEquiv N).trans <| (divisionCoordinatesEquiv N k).trans <|
    (kRestrictedEquiv N k).symm.prodCongr (differencesEquiv N).symm

/-- The restricted component of the decomposition has differences equal to the remainders. -/
theorem difference_decompositionEquiv_fst (hk : 0 < k) (p : PartitionVector N) (i : Fin N) :
    (decompositionEquiv N k hk p).1.1.difference i = p.difference i % k := by
  let _ : NeZero k := ⟨hk.ne'⟩
  rw [← differencesEquiv_apply, ← differencesEquiv_apply]
  simp [decompositionEquiv, divisionCoordinatesEquiv]

/-- The quotient component of the decomposition has differences equal to the quotients. -/
theorem difference_decompositionEquiv_snd (hk : 0 < k) (p : PartitionVector N) (i : Fin N) :
    (decompositionEquiv N k hk p).2.difference i = p.difference i / k := by
  rw [← differencesEquiv_apply, ← differencesEquiv_apply]
  simp [decompositionEquiv, divisionCoordinatesEquiv]

/-- The two components supplied by `decompositionEquiv` reconstruct the original partition
vector as `ρ + k • ν`. -/
theorem eq_add_smul_decompositionEquiv (hk : 0 < k) (p : PartitionVector N) :
    p = (decompositionEquiv N k hk p).1.1 + k • (decompositionEquiv N k hk p).2 := by
  apply (differencesEquiv N).injective
  funext i
  rw [differencesEquiv_apply, differencesEquiv_apply, difference_add, difference_smul,
    difference_decompositionEquiv_fst, difference_decompositionEquiv_snd]
  exact (Nat.mod_add_div (p.difference i) k).symm

/-- The inverse of `decompositionEquiv` sends `(ρ, ν)` to `ρ + k • ν`. -/
theorem decompositionEquiv_symm_apply (hk : 0 < k)
    (p : KRestricted N k × PartitionVector N) :
    (decompositionEquiv N k hk).symm p = p.1.1 + k • p.2 := by
  simpa using eq_add_smul_decompositionEquiv hk ((decompositionEquiv N k hk).symm p)

/-- A proposed restricted part and quotient are the decomposition of `p` exactly when they
reconstruct `p` as `ρ + k • ν`. -/
theorem decompositionEquiv_eq_iff (hk : 0 < k) (p : PartitionVector N)
    (r : KRestricted N k) (q : PartitionVector N) :
    decompositionEquiv N k hk p = (r, q) ↔ p = r.1 + k • q := by
  have hs : (decompositionEquiv N k hk).symm (r, q) = r.1 + k • q :=
    decompositionEquiv_symm_apply hk (r, q)
  constructor
  · intro h
    exact ((decompositionEquiv N k hk).eq_symm_apply.mpr h).trans hs
  · intro h
    exact (decompositionEquiv N k hk).eq_symm_apply.mp (h.trans hs.symm)

/-- Every partition vector has a unique expression `ρ + k • ν`, with `ρ` `k`-restricted. -/
theorem existsUnique_add_smul_of_pos (hk : 0 < k) (p : PartitionVector N) :
    ∃! rq : KRestricted N k × PartitionVector N, p = rq.1.1 + k • rq.2 := by
  refine ⟨decompositionEquiv N k hk p, eq_add_smul_decompositionEquiv hk p, ?_⟩
  intro rq hrq
  exact ((decompositionEquiv_eq_iff hk p rq.1 rq.2).mpr hrq).symm

end PartitionVector

end Nat
