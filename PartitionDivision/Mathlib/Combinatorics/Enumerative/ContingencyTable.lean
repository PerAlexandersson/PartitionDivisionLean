/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi

/-!
# Contingency tables

A *contingency table* with margins `r : ι → ℕ` and `c : κ → ℕ` is a matrix `A : ι → κ → ℕ` of
natural numbers whose `i`-th row sums to `r i` and whose `j`-th column sums to `c j`.  For finite
index types there are finitely many of them, and transposition exchanges the tables with margins
`(r, c)` and those with margins `(c, r)`.

Contingency tables index the monomial expansion of Cauchy-type kernels
`∏_{i,j} f(x_i y_j)`: the coefficient of `x^c y^r` is a sum over the tables with margins `(r, c)`.
The transposition symmetry below is the combinatorial content of the symmetry `x ↔ y` of such a
kernel.

## Main definitions

* `Finset.contingencyTables r c`: the finset of contingency tables with row sums `r` and column
  sums `c`.

## Main results

* `Finset.mem_contingencyTables`: membership is exactly the two margin conditions.
* `Finset.sum_contingencyTables_comm`: a sum over the tables with margins `(r, c)` equals the sum
  of the transposed summand over the tables with margins `(c, r)`.
-/

@[expose] public section

open Finset

namespace Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **The contingency tables with row sums `r` and column sums `c`**: the matrices `A : ι → κ → ℕ`
with `∑ j, A i j = r i` for every row `i` and `∑ i, A i j = c j` for every column `j`.  Every entry
is bounded by its row sum, which is what makes this a finset; `Finset.mem_contingencyTables` is
the characterization to use. -/
def contingencyTables (r : ι → ℕ) (c : κ → ℕ) : Finset (ι → κ → ℕ) :=
  {A ∈ Fintype.piFinset fun i ↦ Fintype.piFinset fun _ ↦ range (r i + 1) |
    (∀ i, ∑ j, A i j = r i) ∧ ∀ j, ∑ i, A i j = c j}

/-- A matrix is a contingency table with margins `(r, c)` exactly when its rows sum to `r` and its
columns sum to `c`. -/
@[simp]
theorem mem_contingencyTables {r : ι → ℕ} {c : κ → ℕ} {A : ι → κ → ℕ} :
    A ∈ contingencyTables r c ↔ (∀ i, ∑ j, A i j = r i) ∧ ∀ j, ∑ i, A i j = c j := by
  simp only [contingencyTables, mem_filter, Fintype.mem_piFinset, mem_range,
    and_iff_right_iff_imp]
  rintro ⟨hr, -⟩ i j
  rw [Nat.lt_succ_iff, ← hr i]
  exact single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ j)

/-- **Transposition of contingency tables**: a sum over the tables with row sums `r` and column
sums `c` equals the sum of the transposed summand over the tables with row sums `c` and column
sums `r`. -/
theorem sum_contingencyTables_comm {M : Type*} [AddCommMonoid M] (r : ι → ℕ) (c : κ → ℕ)
    (F : (ι → κ → ℕ) → M) :
    ∑ A ∈ contingencyTables r c, F A = ∑ A ∈ contingencyTables c r, F fun i j ↦ A j i := by
  refine sum_nbij' (fun A j i ↦ A i j) (fun A i j ↦ A j i) (fun A hA ↦ ?_) (fun A hA ↦ ?_)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun _ _ ↦ rfl
  · simp only [mem_contingencyTables] at hA ⊢
    exact ⟨hA.2, hA.1⟩
  · simp only [mem_contingencyTables] at hA ⊢
    exact ⟨hA.2, hA.1⟩

end Finset
