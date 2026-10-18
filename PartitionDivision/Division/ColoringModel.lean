/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import PartitionDivision.Mathlib.RingTheory.MvPolynomial.ExponentFilter

/-!
# The coloring model of partition division

Fix row lengths `len : Fin m → ℕ` and let `Cell len` be the set of cells `(i, a)`, `a < len i`.
Let `k > 0`.  A *row-block partition* is a set partition `P` of the cells into blocks of `k`
cells with no two cells of a block in the same row.  Its *block graph* `G_P` has the blocks as
vertices, two blocks being adjacent when their closed row intervals `[min row, max row]` meet.

`coloring_identity` states, in `N` variables,

  `(∏ i, (len i)!) • R_k(e_{len 1} ⋯ e_{len m}) = Σ_P X_{G_P}`,

where `R_k = exponentDiv k` and `X_G` is the chromatic symmetric function in `N` colors.  For the
rows of a partition `μ` this is the coloring proposition of the manuscript.

The proof compares coefficients.  The left side is the sum over the row-injective colorings `κ`
of the cells whose color classes all have size divisible by `k`.  A pair `(P, c)` with `c` a
proper coloring of `G_P` gives such a coloring, and conversely the partition is recovered by
cutting each color class, ordered by rows, into consecutive blocks of `k` cells
(`canonicalPartition`).
-/

@[expose] public section

noncomputable section

open Finset MvPolynomial

namespace PartitionDivision.ColoringModel

variable {m : ℕ}

/-- The cells `(i, a)` with `a < len i`. -/
abbrev Cell (len : Fin m → ℕ) := Σ i : Fin m, Fin (len i)

variable {len : Fin m → ℕ}

/-- A partition of the cells into blocks of `k` cells, no two of them in the same row. -/
def IsRowBlockPartition (k : ℕ) (P : Finpartition (univ : Finset (Cell len))) : Prop :=
  ∀ B ∈ P.parts, #B = k ∧ ∀ v ∈ B, ∀ w ∈ B, v.1 = w.1 → v = w

/-- The closed row intervals `[min row, max row]` of two nonempty sets of cells meet. -/
def RowIntervalsMeet (B B' : Finset (Cell len)) : Prop :=
  (∃ v ∈ B, ∃ w ∈ B', v.1 ≤ w.1) ∧ (∃ v ∈ B', ∃ w ∈ B, v.1 ≤ w.1)

theorem rowIntervalsMeet_comm (B B' : Finset (Cell len)) :
    RowIntervalsMeet B B' ↔ RowIntervalsMeet B' B :=
  And.comm

/-- The block graph `G_P`: the blocks of `P`, adjacent when their row intervals meet. -/
def blockGraph (P : Finpartition (univ : Finset (Cell len))) : SimpleGraph P.parts :=
  SimpleGraph.fromRel fun B B' ↦ RowIntervalsMeet B.1 B'.1

theorem blockGraph_adj (P : Finpartition (univ : Finset (Cell len))) (B B' : P.parts) :
    (blockGraph P).Adj B B' ↔ B ≠ B' ∧ RowIntervalsMeet B.1 B'.1 := by
  rw [blockGraph, SimpleGraph.fromRel_adj, rowIntervalsMeet_comm B'.1, or_self]

/-- The chromatic symmetric function of a finite graph in `N` colors: the sum over the proper
colorings `c` of `∏ v, x_{c v}`. -/
def chromaticSymmetric {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (N : ℕ) :
    MvPolynomial (Fin N) ℤ := by
  classical
  exact ∑ c : V → Fin N, if ∀ v w, G.Adj v w → c v ≠ c w then ∏ v, X (c v) else 0

/-! ### Injective words and elementary symmetric polynomials -/

/-- Injective maps `Fin r → Fin N` with a given image correspond to orderings of the image. -/
private theorem card_injective_image_eq {N r : ℕ} (t : Finset (Fin N)) (ht : #t = r) :
    #(univ.filter fun f : Fin r → Fin N ↦ Function.Injective f ∧ univ.image f = t) =
      r.factorial := by
  classical
  have e : {f : Fin r → Fin N // f ∈ univ.filter fun f : Fin r → Fin N ↦
      Function.Injective f ∧ univ.image f = t} ≃ (Fin r ≃ t) :=
    { toFun f :=
        have hf := (Finset.mem_filter.mp f.2).2
        Equiv.ofBijective (fun a ↦ ⟨f.1 a, by
            have hmem : f.1 a ∈ univ.image f.1 := mem_image_of_mem _ (mem_univ a)
            rwa [hf.2] at hmem⟩)
          ⟨fun a b h ↦ hf.1 (congrArg Subtype.val h), fun y ↦ by
            have hy : y.1 ∈ univ.image f.1 := by rw [hf.2]; exact y.2
            obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hy
            exact ⟨a, Subtype.ext ha⟩⟩
      invFun e := ⟨fun a ↦ (e a : Fin N), by
        rw [Finset.mem_filter]
        refine ⟨mem_univ _, fun a b h ↦ e.injective (Subtype.ext h), ?_⟩
        ext y
        simp only [Finset.mem_image, mem_univ, true_and]
        constructor
        · rintro ⟨a, rfl⟩
          exact (e a).2
        · intro hy
          exact ⟨e.symm ⟨y, hy⟩, by simp⟩⟩
      left_inv f := by
        ext a
        rfl
      right_inv e := by
        ext a
        rfl }
  let e0 : Fin r ≃ t := (finCongr ht.symm).trans t.equivFin.symm
  rw [← Fintype.card_coe, Fintype.card_congr (e.trans (Equiv.equivCongr (Equiv.refl _) e0.symm)),
    Fintype.card_perm, Fintype.card_fin]

/-- `r! e_r` is the sum over the injective words of length `r`. -/
theorem sum_injective_prod_X (N r : ℕ) :
    ∑ f ∈ univ.filter (fun f : Fin r → Fin N ↦ Function.Injective f), ∏ a, (X (f a) :
      MvPolynomial (Fin N) ℤ) = r.factorial • esymm (Fin N) ℤ r := by
  classical
  rw [esymm, Finset.smul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun f : Fin r → Fin N ↦ univ.image f)
    (t := powersetCard r univ)]
  · refine Finset.sum_congr rfl fun t ht ↦ ?_
    have hcard : #t = r := (Finset.mem_powersetCard.mp ht).2
    have hval : ∀ f ∈ (univ.filter fun f : Fin r → Fin N ↦ Function.Injective f).filter
        (fun f ↦ univ.image f = t), ∏ a, (X (f a) : MvPolynomial (Fin N) ℤ) = ∏ i ∈ t, X i := by
      intro f hf
      simp only [Finset.mem_filter, mem_univ, true_and] at hf
      rw [← hf.2, Finset.prod_image fun a _ b _ h ↦ hf.1 h]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, Finset.filter_filter]
    rw [card_injective_image_eq t hcard]
  · intro f hf
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ (Finset.mem_filter.mp hf).2, Finset.card_univ,
      Fintype.card_fin]

/-! ### Row-injective colorings of the cells -/

/-- A coloring of the cells is row-injective when cells in the same row get distinct colors. -/
def IsRowInjective {N : ℕ} (κ : Cell len → Fin N) : Prop :=
  ∀ v w : Cell len, v.1 = w.1 → κ v = κ w → v = w

/-- The color content of a coloring: the number of cells of each color. -/
def colorContent {N : ℕ} (κ : Cell len → Fin N) : Fin N →₀ ℕ :=
  ∑ v, Finsupp.single (κ v) 1

theorem prod_X_eq_monomial_colorContent {N : ℕ} (κ : Cell len → Fin N) :
    ∏ v, (X (κ v) : MvPolynomial (Fin N) ℤ) = monomial (colorContent κ) 1 := by
  rw [colorContent, monomial_sum_one]
  rfl

open Classical in
/-- `(∏ i, (len i)!) e_{len 1} ⋯ e_{len m}` is the sum over the row-injective colorings of the
cells. -/
theorem prod_factorial_smul_prod_esymm (N : ℕ) :
    (∏ i, (len i).factorial) • ∏ i, esymm (Fin N) ℤ (len i) =
      ∑ κ ∈ univ.filter (IsRowInjective (N := N) (len := len)),
        monomial (colorContent κ) (1 : ℤ) := by
  simp only [nsmul_eq_mul, Nat.cast_prod, ← Finset.prod_mul_distrib]
  have hrow (i : Fin m) : ((len i).factorial : MvPolynomial (Fin N) ℤ) * esymm (Fin N) ℤ (len i) =
      ∑ f ∈ univ.filter (fun f : Fin (len i) → Fin N ↦ Function.Injective f),
        ∏ a, (X (f a) : MvPolynomial (Fin N) ℤ) := by
    rw [sum_injective_prod_X, nsmul_eq_mul]
  simp_rw [hrow]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_nbij' (fun F v ↦ F v.1 v.2) (fun κ i a ↦ κ ⟨i, a⟩) ?_ ?_ ?_ ?_ ?_
  · intro F hF
    rw [Fintype.mem_piFinset] at hF
    rw [Finset.mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rintro ⟨i, a⟩ ⟨i', b⟩ hrow heq
    simp only at hrow
    subst hrow
    have hinj := (Finset.mem_filter.mp (hF i)).2
    have hab : a = b := hinj heq
    rw [hab]
  · intro κ hκ
    rw [Finset.mem_filter] at hκ
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_filter]
    refine ⟨mem_univ _, fun a b h ↦ ?_⟩
    have := hκ.2 ⟨i, a⟩ ⟨i, b⟩ rfl h
    exact eq_of_heq (Sigma.mk.inj this).2
  · intro F _
    rfl
  · intro κ _
    rfl
  · intro F _
    rw [← prod_X_eq_monomial_colorContent, Fintype.prod_sigma]

open Classical in
/-- The left side of the coloring identity as a sum over row-injective colorings. -/
theorem prod_factorial_smul_exponentDiv (k N : ℕ) :
    (∏ i, (len i).factorial) • exponentDiv k (∏ i, esymm (Fin N) ℤ (len i)) =
      ∑ κ ∈ univ.filter (IsRowInjective (N := N) (len := len)),
        if ExponentsDivisibleBy k (colorContent κ) then
          monomial (exponentQuotient k (colorContent κ)) (1 : ℤ)
        else 0 := by
  rw [← map_nsmul, prod_factorial_smul_prod_esymm, map_sum]
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  rw [exponentDiv_monomial]

/-! ### Proper colorings of the block graph as colorings of the cells -/

/-- A coloring of the cells is compatible with `P` when it is constant on the blocks of `P` and
gives different colors to blocks whose row intervals meet. -/
def IsCompatible {N : ℕ} (P : Finpartition (univ : Finset (Cell len))) (κ : Cell len → Fin N) :
    Prop :=
  (∀ v w, w ∈ P.part v → κ v = κ w) ∧
    ∀ v w, P.part v ≠ P.part w → RowIntervalsMeet (P.part v) (P.part w) → κ v ≠ κ w

theorem part_mem_parts (P : Finpartition (univ : Finset (Cell len))) (v : Cell len) :
    P.part v ∈ P.parts :=
  P.part_mem.2 (mem_univ v)

theorem mem_part_self (P : Finpartition (univ : Finset (Cell len))) (v : Cell len) :
    v ∈ P.part v :=
  P.mem_part (mem_univ v)

/-- A cell of a block. -/
def blockRep (P : Finpartition (univ : Finset (Cell len))) (B : P.parts) : Cell len :=
  (P.nonempty_of_mem_parts B.2).choose

theorem blockRep_mem (P : Finpartition (univ : Finset (Cell len))) (B : P.parts) :
    blockRep P B ∈ B.1 :=
  (P.nonempty_of_mem_parts B.2).choose_spec

theorem part_blockRep (P : Finpartition (univ : Finset (Cell len))) (B : P.parts) :
    P.part (blockRep P B) = B.1 :=
  P.part_eq_of_mem B.2 (blockRep_mem P B)

/-- The color content of a coloring constant on the blocks of a row-block partition. -/
theorem colorContent_comp_part {k N : ℕ} {P : Finpartition (univ : Finset (Cell len))}
    (hP : IsRowBlockPartition k P) (c : P.parts → Fin N) :
    colorContent (fun v ↦ c ⟨P.part v, part_mem_parts P v⟩) =
      k • ∑ B : P.parts, Finsupp.single (c B) 1 := by
  classical
  have h1 : (∑ v : Cell len, Finsupp.single (c ⟨P.part v, part_mem_parts P v⟩) (1 : ℕ)) =
      ∑ B ∈ P.parts, ∑ v ∈ id B, Finsupp.single (c ⟨P.part v, part_mem_parts P v⟩) 1 := by
    rw [← Finset.sum_biUnion P.supIndep.pairwiseDisjoint]
    exact Finset.sum_congr P.biUnion_parts.symm fun _ _ ↦ rfl
  rw [colorContent, h1, ← Finset.sum_attach, Finset.univ_eq_attach, Finset.smul_sum]
  refine Finset.sum_congr rfl fun B _ ↦ ?_
  have hval : ∀ v ∈ id B.1, Finsupp.single (c ⟨P.part v, part_mem_parts P v⟩) 1 =
      Finsupp.single (c B) (1 : ℕ) := by
    intro v hv
    have hp : (⟨P.part v, part_mem_parts P v⟩ : P.parts) = B :=
      Subtype.ext (P.part_eq_of_mem B.2 hv)
    rw [hp]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, id_eq, (hP B.1 B.2).1]

theorem exponentQuotient_nsmul {k : ℕ} (hk : 0 < k) {σ : Type*} (d : σ →₀ ℕ) :
    exponentQuotient k (k • d) = d := by
  ext i
  simp [Nat.mul_div_cancel_left _ hk]

open Classical in
/-- The chromatic symmetric function of the block graph, as a sum over compatible colorings of
the cells. -/
theorem chromaticSymmetric_blockGraph {k : ℕ} (hk : 0 < k) (N : ℕ)
    {P : Finpartition (univ : Finset (Cell len))} (hP : IsRowBlockPartition k P) :
    chromaticSymmetric (blockGraph P) N =
      ∑ κ ∈ univ.filter (IsCompatible (N := N) P),
        monomial (exponentQuotient k (colorContent κ)) (1 : ℤ) := by
  rw [chromaticSymmetric, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun c v ↦ c ⟨P.part v, part_mem_parts P v⟩)
    (fun κ B ↦ κ (blockRep P B)) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_filter] at hc ⊢
    refine ⟨mem_univ _, ?_, ?_⟩
    · intro v w hw
      have : P.part w = P.part v := P.part_eq_of_mem (part_mem_parts P v) hw
      simp only [this]
    · intro v w hne hmeet
      apply hc.2
      rw [blockGraph_adj]
      exact ⟨fun h ↦ hne (congrArg Subtype.val h), hmeet⟩
  · intro κ hκ
    rw [Finset.mem_filter] at hκ ⊢
    refine ⟨mem_univ _, ?_⟩
    intro B B' hadj
    rw [blockGraph_adj] at hadj
    apply hκ.2.2
    · rw [part_blockRep, part_blockRep]
      exact fun h ↦ hadj.1 (Subtype.ext h)
    · rw [part_blockRep, part_blockRep]
      exact hadj.2
  · intro c _
    funext B
    exact congrArg c (Subtype.ext (part_blockRep P B))
  · intro κ hκ
    rw [Finset.mem_filter] at hκ
    funext v
    exact (hκ.2.1 v _ (blockRep_mem P ⟨P.part v, part_mem_parts P v⟩)).symm
  · intro c _
    rw [colorContent_comp_part hP, exponentQuotient_nsmul hk, monomial_sum_one]
    rfl

/-! ### The canonical partition of a coloring -/

/-- The cells of color `γ`. -/
def colorClass {N : ℕ} (κ : Cell len → Fin N) (γ : Fin N) : Finset (Cell len) :=
  univ.filter fun v ↦ κ v = γ

theorem mem_colorClass {N : ℕ} {κ : Cell len → Fin N} {γ : Fin N} {v : Cell len} :
    v ∈ colorClass κ γ ↔ κ v = γ := by
  simp [colorClass]

theorem colorContent_apply {N : ℕ} (κ : Cell len → Fin N) (γ : Fin N) :
    colorContent κ γ = #(colorClass κ γ) := by
  classical
  rw [colorContent, Finsupp.finsetSum_apply, colorClass, Finset.card_filter]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [Finsupp.single_apply]

/-- The number of cells of the color of `v` in earlier rows. -/
def rowRank {N : ℕ} (κ : Cell len → Fin N) (v : Cell len) : ℕ :=
  #((colorClass κ (κ v)).filter fun w ↦ w.1 < v.1)

/-- The color of `v` and the index of the block of `k` consecutive cells of that color, ordered by
rows, that contains `v`. -/
def blockKey {N : ℕ} (k : ℕ) (κ : Cell len → Fin N) (v : Cell len) : Fin N × ℕ :=
  (κ v, rowRank κ v / k)

open Classical in
/-- Cut each color class, ordered by rows, into consecutive blocks of `k` cells. -/
def canonicalPartition {N : ℕ} (k : ℕ) (κ : Cell len → Fin N) :
    Finpartition (univ : Finset (Cell len)) :=
  Finpartition.ofSetoid (Setoid.ker (blockKey k κ))

theorem mem_part_canonicalPartition {N k : ℕ} {κ : Cell len → Fin N} {v w : Cell len} :
    w ∈ (canonicalPartition k κ).part v ↔ blockKey k κ v = blockKey k κ w := by
  classical
  rw [canonicalPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

theorem rowRank_le_of_le {N : ℕ} {κ : Cell len → Fin N} {u w : Cell len} (hc : κ u = κ w)
    (h : u.1 ≤ w.1) : rowRank κ u ≤ rowRank κ w := by
  rw [rowRank, rowRank, hc]
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩

theorem rowRank_lt_of_lt {N : ℕ} {κ : Cell len → Fin N} {u w : Cell len} (hc : κ u = κ w)
    (h : u.1 < w.1) : rowRank κ u < rowRank κ w := by
  rw [rowRank, rowRank, hc]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨u, ?_, ?_⟩
    · rw [Finset.mem_filter, mem_colorClass]
      exact ⟨hc, h⟩
    · rw [Finset.mem_filter]
      exact fun hu ↦ lt_irrefl _ hu.2
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩

theorem rowRank_lt_card {N : ℕ} (κ : Cell len → Fin N) (v : Cell len) :
    rowRank κ v < #(colorClass κ (κ v)) := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  refine ⟨v, mem_colorClass.mpr rfl, ?_⟩
  rw [Finset.mem_filter]
  exact fun hv ↦ lt_irrefl _ hv.2

theorem rowRank_injOn {N : ℕ} {κ : Cell len → Fin N} (hκ : IsRowInjective κ) (γ : Fin N) :
    Set.InjOn (rowRank κ) (colorClass κ γ) := by
  intro u hu w hw h
  rw [Finset.mem_coe, mem_colorClass] at hu hw
  have hc : κ u = κ w := hu.trans hw.symm
  rcases lt_trichotomy u.1 w.1 with hlt | heq | hgt
  · exact absurd h (rowRank_lt_of_lt hc hlt).ne
  · exact hκ u w heq hc
  · exact absurd h (rowRank_lt_of_lt hc.symm hgt).ne'

theorem image_rowRank {N : ℕ} {κ : Cell len → Fin N} (hκ : IsRowInjective κ) (γ : Fin N) :
    (colorClass κ γ).image (rowRank κ) = range #(colorClass κ γ) := by
  apply Finset.eq_of_subset_of_card_le
  · intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    rw [Finset.mem_range]
    have := rowRank_lt_card κ v
    rwa [(mem_colorClass.mp hv)] at this
  · rw [Finset.card_range, Finset.card_image_of_injOn (rowRank_injOn hκ γ)]

theorem card_filter_div_range {k M j : ℕ} (hk : 0 < k) (hj : j < M) :
    #((range (k * M)).filter fun r ↦ r / k = j) = k := by
  have h : (range (k * M)).filter (fun r ↦ r / k = j) = Ico (j * k) (j * k + k) := by
    ext r
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨_, rfl⟩
      exact ⟨Nat.div_mul_le_self r k, by
        have := Nat.lt_div_mul_add (a := r) hk
        lia⟩
    · rintro ⟨h1, h2⟩
      have hdiv : r / k = j := by
        rw [Nat.div_eq_iff hk]
        constructor <;> lia
      refine ⟨?_, hdiv⟩
      have : j + 1 ≤ M := hj
      calc r < j * k + k := h2
        _ = (j + 1) * k := by ring
        _ ≤ M * k := Nat.mul_le_mul_right k this
        _ = k * M := by ring
  rw [h, Nat.card_Ico]
  lia

/-- Two finpartitions of a finite type with the same parts of every element are equal. -/
theorem finpartition_eq_of_mem_part_iff {α : Type*} [Fintype α] [DecidableEq α]
    {P Q : Finpartition (univ : Finset α)} (h : ∀ v w, w ∈ P.part v ↔ w ∈ Q.part v) :
    P = Q := by
  have key : ∀ (P Q : Finpartition (univ : Finset α)),
      (∀ v w, w ∈ P.part v ↔ w ∈ Q.part v) → ∀ B ∈ P.parts, B ∈ Q.parts := by
    intro P Q h B hB
    obtain ⟨v, hv⟩ := P.nonempty_of_mem_parts hB
    have hP : P.part v = B := P.part_eq_of_mem hB hv
    have hQ : Q.part v = B := by
      ext w
      rw [← h, hP]
    rw [← hQ]
    exact Q.part_mem.2 (mem_univ v)
  apply Finpartition.ext
  ext B
  exact ⟨key P Q h B, key Q P (fun v w ↦ (h v w).symm) B⟩

theorem part_canonicalPartition_eq {N k : ℕ} (κ : Cell len → Fin N) (v : Cell len) :
    (canonicalPartition k κ).part v =
      (colorClass κ (κ v)).filter fun w ↦ rowRank κ w / k = rowRank κ v / k := by
  ext w
  rw [mem_part_canonicalPartition, Finset.mem_filter, mem_colorClass, blockKey, blockKey,
    Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩

theorem card_part_canonicalPartition {N k : ℕ} (hk : 0 < k) {κ : Cell len → Fin N}
    (hκ : IsRowInjective κ) (hdiv : ExponentsDivisibleBy k (colorContent κ)) (v : Cell len) :
    #((canonicalPartition k κ).part v) = k := by
  rw [part_canonicalPartition_eq]
  obtain ⟨M, hM⟩ : k ∣ #(colorClass κ (κ v)) := by
    rw [← colorContent_apply]
    exact hdiv (κ v)
  have hj : rowRank κ v / k < M := by
    rw [Nat.div_lt_iff_lt_mul hk, mul_comm, ← hM]
    exact rowRank_lt_card κ v
  have h1 : #((colorClass κ (κ v)).filter fun w ↦ rowRank κ w / k = rowRank κ v / k) =
      #(((colorClass κ (κ v)).image (rowRank κ)).filter fun r ↦ r / k = rowRank κ v / k) := by
    rw [Finset.filter_image, Finset.card_image_of_injOn]
    exact (rowRank_injOn hκ (κ v)).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  rw [h1, image_rowRank hκ, hM, card_filter_div_range hk hj]

/-- The canonical partition of a row-injective coloring with color counts divisible by `k` is a
row-block partition. -/
theorem isRowBlockPartition_canonicalPartition {N k : ℕ} (hk : 0 < k) {κ : Cell len → Fin N}
    (hκ : IsRowInjective κ) (hdiv : ExponentsDivisibleBy k (colorContent κ)) :
    IsRowBlockPartition k (canonicalPartition k κ) := by
  intro B hB
  obtain ⟨v, hv⟩ := (canonicalPartition k κ).nonempty_of_mem_parts hB
  have hBv : (canonicalPartition k κ).part v = B :=
    (canonicalPartition k κ).part_eq_of_mem hB hv
  rw [← hBv]
  refine ⟨card_part_canonicalPartition hk hκ hdiv v, ?_⟩
  intro u hu w hw hrow
  rw [part_canonicalPartition_eq, Finset.mem_filter, mem_colorClass] at hu hw
  exact hκ u w hrow (hu.1.trans hw.1.symm)

private theorem lt_of_div_lt_div' {a b k : ℕ} (h : a / k < b / k) : a < b := by
  by_contra hle
  exact absurd (Nat.div_le_div_right (not_lt.mp hle)) (not_le.mpr h)

/-- A coloring is compatible with its canonical partition. -/
theorem isCompatible_canonicalPartition {N k : ℕ} (κ : Cell len → Fin N) :
    IsCompatible (canonicalPartition k κ) κ := by
  refine ⟨fun v w hw ↦ ?_, fun v w hne hmeet heq ↦ ?_⟩
  · rw [mem_part_canonicalPartition] at hw
    exact congrArg Prod.fst hw
  · have hj : rowRank κ v / k ≠ rowRank κ w / k := by
      intro hj
      apply hne
      have hw : w ∈ (canonicalPartition k κ).part v :=
        mem_part_canonicalPartition.mpr (Prod.ext heq hj)
      exact ((canonicalPartition k κ).part_eq_of_mem (part_mem_parts _ v) hw).symm
    have below : ∀ {a b : Cell len}, κ a = κ b → rowRank κ a / k < rowRank κ b / k →
        ∀ u ∈ (canonicalPartition k κ).part a, ∀ x ∈ (canonicalPartition k κ).part b,
          u.1 < x.1 := by
      intro a b hab hlt u hu x hx
      rw [part_canonicalPartition_eq, Finset.mem_filter, mem_colorClass] at hu hx
      have hux : κ u = κ x := hu.1.trans (hab.trans hx.1.symm)
      have hr : rowRank κ u < rowRank κ x := lt_of_div_lt_div' (by rw [hu.2, hx.2]; exact hlt)
      by_contra hle
      exact absurd (rowRank_le_of_le hux.symm (not_lt.mp hle)) (not_le.mpr hr)
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · obtain ⟨a, ha, b, hb, hab⟩ := hmeet.2
      exact absurd hab (not_le.mpr (below heq hlt b hb a ha))
    · obtain ⟨a, ha, b, hb, hab⟩ := hmeet.1
      exact absurd hab (not_le.mpr (below heq.symm hgt b hb a ha))

/-! ### A compatible row-block partition is canonical -/

section Compatible

variable {N k : ℕ} {P : Finpartition (univ : Finset (Cell len))} {κ : Cell len → Fin N}

theorem isRowInjective_of_isCompatible (hP : IsRowBlockPartition k P) (hc : IsCompatible P κ) :
    IsRowInjective κ := by
  intro v w hrow hcol
  by_cases hw : w ∈ P.part v
  · exact (hP _ (part_mem_parts P v)).2 v (mem_part_self P v) w hw hrow
  · exfalso
    have hne : P.part v ≠ P.part w := fun h ↦ hw (h ▸ mem_part_self P w)
    exact hc.2 v w hne ⟨⟨v, mem_part_self P v, w, mem_part_self P w, hrow.le⟩,
      ⟨w, mem_part_self P w, v, mem_part_self P v, hrow.ge⟩⟩ hcol

theorem exponentsDivisibleBy_of_isCompatible (hP : IsRowBlockPartition k P)
    (hc : IsCompatible P κ) : ExponentsDivisibleBy k (colorContent κ) := by
  classical
  intro γ
  rw [colorContent_apply]
  have h : colorClass κ γ = P.parts.biUnion fun B ↦ B.filter fun u ↦ κ u = γ := by
    ext v
    simp only [mem_colorClass, Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨P.part v, part_mem_parts P v, mem_part_self P v, h⟩
    · rintro ⟨B, _, _, h⟩
      exact h
  rw [h, Finset.card_biUnion]
  · apply Finset.dvd_sum
    intro B hB
    by_cases hγ : ∃ u ∈ B, κ u = γ
    · obtain ⟨u, hu, huγ⟩ := hγ
      have hfilter : B.filter (fun u ↦ κ u = γ) = B := by
        apply Finset.filter_true_of_mem
        intro x hx
        have hBu : P.part u = B := P.part_eq_of_mem hB hu
        rw [← huγ]
        exact (hc.1 u x (hBu ▸ hx)).symm
      rw [hfilter, (hP B hB).1]
    · have hfilter : B.filter (fun u ↦ κ u = γ) = ∅ :=
        Finset.filter_false_of_mem fun x hx h ↦ hγ ⟨x, hx, h⟩
      rw [hfilter, Finset.card_empty]
      exact dvd_zero k
  · intro B hB B' hB' hne
    exact Finset.disjoint_filter_filter (P.disjoint hB hB' hne)

/-- The blocks of the color of `v` lying entirely below the block of `v`. -/
def blocksBelow (P : Finpartition (univ : Finset (Cell len))) (κ : Cell len → Fin N)
    (v : Cell len) : Finset (Finset (Cell len)) := by
  classical
  exact P.parts.filter fun B ↦ B ≠ P.part v ∧ (∀ u ∈ B, κ u = κ v) ∧
    ∀ u ∈ B, ∀ x ∈ P.part v, u.1 < x.1

theorem rowRank_eq (hP : IsRowBlockPartition k P) (hc : IsCompatible P κ) (v : Cell len) :
    rowRank κ v = k * #(blocksBelow P κ v) + #((P.part v).filter fun u ↦ u.1 < v.1) := by
  classical
  have h : (colorClass κ (κ v)).filter (fun w ↦ w.1 < v.1) =
      P.parts.biUnion fun B ↦ B.filter fun u ↦ κ u = κ v ∧ u.1 < v.1 := by
    ext w
    simp only [Finset.mem_filter, mem_colorClass, Finset.mem_biUnion]
    constructor
    · intro h
      exact ⟨P.part w, part_mem_parts P w, mem_part_self P w, h⟩
    · rintro ⟨B, _, _, h⟩
      exact h
  have hcard := Finset.card_biUnion (s := P.parts)
    (t := fun B ↦ B.filter fun u ↦ κ u = κ v ∧ u.1 < v.1)
    (fun B hB B' hB' hne ↦ Finset.disjoint_filter_filter (P.disjoint hB hB' hne))
  rw [rowRank, h, hcard]
  have hpoint : ∀ B ∈ P.parts, #(B.filter fun u ↦ κ u = κ v ∧ u.1 < v.1) =
      (if B = P.part v then #((P.part v).filter fun u ↦ u.1 < v.1) else 0) +
        (if B ∈ blocksBelow P κ v then k else 0) := by
    intro B hB
    by_cases hBv : B = P.part v
    · have hnot : B ∉ blocksBelow P κ v := by
        rw [blocksBelow, Finset.mem_filter]
        exact fun h ↦ h.2.1 hBv
      rw [ite_eq_left hBv, ite_eq_right hnot, add_zero, hBv]
      congr 1
      apply Finset.filter_congr
      intro u hu
      have := hc.1 v u hu
      simp [this]
    · rw [ite_eq_right hBv, zero_add]
      by_cases hS : B ∈ blocksBelow P κ v
      · rw [ite_eq_left hS]
        rw [blocksBelow, Finset.mem_filter] at hS
        rw [← (hP B hB).1]
        congr 1
        apply Finset.filter_true_of_mem
        intro u hu
        exact ⟨hS.2.2.1 u hu, hS.2.2.2 u hu v (mem_part_self P v)⟩
      · rw [ite_eq_right hS]
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_false_of_mem
        rintro u hu ⟨hcol, hrow⟩
        apply hS
        have hBu : P.part u = B := P.part_eq_of_mem hB hu
        have hcolB : ∀ x ∈ B, κ x = κ v := by
          intro x hx
          rw [← hcol]
          exact (hc.1 u x (hBu ▸ hx)).symm
        have hnotmeet : ¬ RowIntervalsMeet B (P.part v) := by
          intro hmeet
          apply hc.2 u v (by rw [hBu]; exact hBv) (by rw [hBu]; exact hmeet)
          exact hcol
        rw [blocksBelow, Finset.mem_filter]
        refine ⟨hB, hBv, hcolB, ?_⟩
        intro x hx y hy
        by_contra hle
        exact hnotmeet ⟨⟨u, hu, v, mem_part_self P v, hrow.le⟩, ⟨y, hy, x, hx, not_lt.mp hle⟩⟩
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_eq_left (part_mem_parts P v), Finset.sum_ite_mem, Finset.sum_const,
    Finset.inter_eq_right.mpr (by unfold blocksBelow; exact Finset.filter_subset _ _),
    smul_eq_mul]
  ring

theorem rowRank_div_eq (hk : 0 < k) (hP : IsRowBlockPartition k P) (hc : IsCompatible P κ)
    (v : Cell len) : rowRank κ v / k = #(blocksBelow P κ v) := by
  rw [rowRank_eq hP hc, Nat.mul_add_div hk, Nat.div_eq_of_lt, add_zero]
  rw [← (hP _ (part_mem_parts P v)).1]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  refine ⟨v, mem_part_self P v, ?_⟩
  rw [Finset.mem_filter]
  exact fun h ↦ lt_irrefl _ h.2

theorem card_blocksBelow_lt (hc : IsCompatible P κ) {v w : Cell len} (hcol : κ v = κ w)
    (hne : P.part v ≠ P.part w)
    (hbelow : ∀ a ∈ P.part v, ∀ b ∈ P.part w, a.1 < b.1) :
    #(blocksBelow P κ v) < #(blocksBelow P κ w) := by
  classical
  have hnot : P.part v ∉ blocksBelow P κ v := by
    rw [blocksBelow, Finset.mem_filter]
    exact fun h ↦ h.2.1 rfl
  have hsub : insert (P.part v) (blocksBelow P κ v) ⊆ blocksBelow P κ w := by
    intro B hB
    rw [Finset.mem_insert] at hB
    rw [blocksBelow, Finset.mem_filter]
    rcases hB with rfl | hB
    · refine ⟨part_mem_parts P v, hne, fun u hu ↦ ?_, hbelow⟩
      rw [← hcol]
      exact (hc.1 v u hu).symm
    · rw [blocksBelow, Finset.mem_filter] at hB
      refine ⟨hB.1, ?_, fun u hu ↦ (hB.2.2.1 u hu).trans hcol, ?_⟩
      · rintro rfl
        have h1 := hB.2.2.2 w (mem_part_self P w) v (mem_part_self P v)
        have h2 := hbelow v (mem_part_self P v) w (mem_part_self P w)
        exact lt_asymm h1 h2
      · intro u hu x hx
        exact (hB.2.2.2 u hu v (mem_part_self P v)).trans
          (hbelow v (mem_part_self P v) x hx)
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at this
  lia

/-- A compatible row-block partition is the canonical partition of the coloring. -/
theorem eq_canonicalPartition (hk : 0 < k) (hP : IsRowBlockPartition k P)
    (hc : IsCompatible P κ) : P = canonicalPartition k κ := by
  classical
  apply finpartition_eq_of_mem_part_iff
  intro v w
  rw [mem_part_canonicalPartition, blockKey, blockKey, Prod.mk.injEq,
    rowRank_div_eq hk hP hc, rowRank_div_eq hk hP hc]
  constructor
  · intro hw
    have hpart : P.part w = P.part v := P.part_eq_of_mem (part_mem_parts P v) hw
    have hcol : κ v = κ w := hc.1 v w hw
    refine ⟨hcol, ?_⟩
    simp only [blocksBelow, hpart, hcol]
  · rintro ⟨hcol, hcard⟩
    by_contra hw
    have hne : P.part v ≠ P.part w := fun h ↦ hw (h ▸ mem_part_self P w)
    have hnotmeet : ¬ RowIntervalsMeet (P.part v) (P.part w) := fun hmeet ↦
      hc.2 v w hne hmeet hcol
    unfold RowIntervalsMeet at hnotmeet
    rw [not_and_or] at hnotmeet
    rcases hnotmeet with h | h
    · push Not at h
      have := card_blocksBelow_lt hc hcol.symm hne.symm (fun a ha b hb ↦ h b hb a ha)
      lia
    · push Not at h
      have := card_blocksBelow_lt hc hcol hne (fun a ha b hb ↦ h b hb a ha)
      lia

end Compatible

/-! ### The coloring identity -/

open Classical in
/-- A coloring has exactly one compatible row-block partition, the canonical one, when it is
row-injective with color counts divisible by `k`, and none otherwise. -/
theorem card_filter_isCompatible {N k : ℕ} (hk : 0 < k) (κ : Cell len → Fin N) :
    #((univ.filter (IsRowBlockPartition k)).filter fun P ↦ IsCompatible P κ) =
      if IsRowInjective κ ∧ ExponentsDivisibleBy k (colorContent κ) then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨canonicalPartition k κ, ?_⟩
    ext P
    simp only [Finset.mem_filter, mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hP, hc⟩
      exact eq_canonicalPartition hk hP hc
    · rintro rfl
      exact ⟨isRowBlockPartition_canonicalPartition hk h.1 h.2,
        isCompatible_canonicalPartition κ⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro P hP hc
    rw [Finset.mem_filter] at hP
    exact h ⟨isRowInjective_of_isCompatible hP.2 hc, exponentsDivisibleBy_of_isCompatible hP.2 hc⟩

open Classical in
/-- **The coloring identity.**  For `0 < k` and row lengths `len`, in `N` variables,

  `(∏ i, (len i)!) • R_k(e_{len 1} ⋯ e_{len m}) = Σ_P X_{G_P}`,

the sum over the partitions `P` of the cells into blocks of `k` cells with no two cells of a block
in the same row, where `G_P` is the intersection graph of the closed row intervals of the blocks
and `X_G` is the chromatic symmetric function in `N` colors. -/
theorem coloring_identity {k : ℕ} (hk : 0 < k) (N : ℕ) :
    (∏ i, (len i).factorial) • exponentDiv k (∏ i, esymm (Fin N) ℤ (len i)) =
      ∑ P ∈ univ.filter (IsRowBlockPartition (len := len) k),
        chromaticSymmetric (blockGraph P) N := by
  have hR : ∀ P ∈ univ.filter (IsRowBlockPartition (len := len) k),
      chromaticSymmetric (blockGraph P) N = ∑ κ : Cell len → Fin N,
        if IsCompatible P κ then monomial (exponentQuotient k (colorContent κ)) (1 : ℤ)
        else 0 := by
    intro P hP
    rw [chromaticSymmetric_blockGraph hk N (Finset.mem_filter.mp hP).2, Finset.sum_filter]
  rw [prod_factorial_smul_exponentDiv, Finset.sum_congr rfl hR, Finset.sum_comm,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  rw [← Finset.sum_filter, Finset.sum_const, card_filter_isCompatible hk κ]
  by_cases h1 : IsRowInjective κ <;> by_cases h2 : ExponentsDivisibleBy k (colorContent κ) <;>
    simp [h1, h2]

open Classical in
/-- **The coloring identity for a partition.**  If the rows have the lengths of the parts of
`μ`, then `(∏_i μ_i!) • R_k(e_μ) = Σ_P X_{G_P}`. -/
theorem coloring_identity_esymmPart {k n : ℕ} (hk : 0 < k) (N : ℕ) (mu : n.Partition)
    (hlen : univ.val.map len = mu.parts) :
    (mu.parts.map Nat.factorial).prod • exponentDiv k (esymmPart (Fin N) ℤ mu) =
      ∑ P ∈ univ.filter (IsRowBlockPartition (len := len) k),
        chromaticSymmetric (blockGraph P) N := by
  have h1 : (mu.parts.map Nat.factorial).prod = ∏ i, (len i).factorial := by
    rw [← hlen, Multiset.map_map]
    rfl
  have h2 : esymmPart (Fin N) ℤ mu = ∏ i, esymm (Fin N) ℤ (len i) := by
    rw [esymmPart, ← hlen, Multiset.map_map]
    rfl
  rw [h1, h2]
  exact coloring_identity hk N

end PartitionDivision.ColoringModel
