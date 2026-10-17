/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# The kernel identity for Macdonald's operators

For variables `x, y : Fin N → K` and a parameter `t`, let

`kernelSum N r t x y = Σ_{|I| = r} ∏_{i∈I, j∉I} (t x_i − x_j)/(x_i − x_j) ·
  ∏_{i∈I} ∏_j (1 − x_i y_j)/(1 − t x_i y_j)`.

`Macdonald.kernelSum_comm` shows that this sum is symmetric under exchanging the two alphabets
(Macdonald, *Symmetric Functions and Hall Polynomials*, Ch. VI §3). This is the `q`-free identity
behind the self-adjointness of the operators `D_N^r` with respect to the `q,t`-pairing.

The proof (induction on the number of variables, comparing a polynomial in an inserted variable
at enough points, then a transfer from the generic point) was found by Aristotle (Harmonic) and
ported to this Mathlib version.
-/

@[expose] public section

namespace Macdonald


open Finset

/-- The coefficient of `X ^ r` in the Macdonald kernel ratio `D_N(X) Π / Π`, without the
common factor `t ^ (r(r-1)/2)`. -/
noncomputable def kernelSum {K : Type*} [Field K] (N r : ℕ) (t : K) (x y : Fin N → K) : K :=
  ∑ I ∈ (univ : Finset (Fin N)).powersetCard r,
    (∏ i ∈ I, ∏ j ∈ univ \ I, (t * x i - x j) / (x i - x j)) *
      ∏ i ∈ I, ∏ j, (1 - x i * y j) / (1 - t * x i * y j)

namespace KernelSymm

/-!
## Proof outline

* `kG S T r t x y` is `kernelSum` for arbitrary finite index sets `S` (first alphabet) and
  `T` (second alphabet).
* `kG_symm`: under the genericity hypotheses `Hyp`, `kG S T r t x y = kG T S r t y x` when
  `S.card = T.card`, proved by induction on the size. Insert one variable `x a` and
  clear denominators to get the polynomial `kP` in `x a`. It has degree `≤ 2n - 1` and
  vanishes at the `2n` points `1 / y k` (where the identity reduces to size `n - 1`, see
  `kG_reduce_left`, `kG_reduce_right`) and `1 / (t y k)` (where the residues of both sides
  agree by the induction hypothesis for `r - 1`, see `kP_eval_w`), so it is zero.
* `kernelSum_comm_aux`: the identity holds at the generic point of `ℤ[t, x_i, y_j]`. Since all
  denominators are nonzero at the given point, it transfers through the localization at
  those denominators.
-/

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

noncomputable def kA (t : K) (x : ι → K) (S I : Finset ι) : K :=
  ∏ i ∈ I, ∏ j ∈ S \ I, (t * x i - x j) / (x i - x j)

noncomputable def kB (t : K) (x y : ι → K) (T I : Finset ι) : K :=
  ∏ i ∈ I, ∏ j ∈ T, (1 - x i * y j) / (1 - t * x i * y j)

noncomputable def kG (S T : Finset ι) (r : ℕ) (t : K) (x y : ι → K) : K :=
  ∑ I ∈ S.powersetCard r, kA t x S I * kB t x y T I

lemma kernelSum_eq_kG (N r : ℕ) (t : K) (x y : Fin N → K) :
    kernelSum N r t x y = kG univ univ r t x y := rfl

lemma kG_zero (S T : Finset ι) (t : K) (x y : ι → K) : kG S T 0 t x y = 1 := by
  simp [kG, kA, kB]

lemma kG_empty_succ (T : Finset ι) (r : ℕ) (t : K) (x y : ι → K) :
    kG ∅ T (r + 1) t x y = 0 := by
  unfold kG
  rw [powersetCard_eq_empty.2 (by simp), sum_empty]

lemma kA_congr {t : K} {x x' : ι → K} {S I : Finset ι} (h : ∀ i ∈ S, x i = x' i) (hI : I ⊆ S) :
    kA t x S I = kA t x' S I := by
  unfold kA
  refine prod_congr rfl fun i hi => prod_congr rfl fun j hj => ?_
  rw [h i (hI hi), h j (sdiff_subset hj)]

omit [DecidableEq ι] in
lemma kB_congr {t : K} {x x' y y' : ι → K} {T I : Finset ι} (hx : ∀ i ∈ I, x i = x' i)
    (hy : ∀ j ∈ T, y j = y' j) : kB t x y T I = kB t x' y' T I := by
  unfold kB
  refine prod_congr rfl fun i hi => prod_congr rfl fun j hj => ?_
  rw [hx i hi, hy j hj]

lemma kG_congr {S T : Finset ι} {r : ℕ} {t : K} {x x' y y' : ι → K} (hx : ∀ i ∈ S, x i = x' i)
    (hy : ∀ j ∈ T, y j = y' j) : kG S T r t x y = kG S T r t x' y' := by
  unfold kG
  refine sum_congr rfl fun I hI => ?_
  have hIS : I ⊆ S := (mem_powersetCard.1 hI).1
  rw [kA_congr hx hIS, kB_congr (fun i hi => hx i (hIS hi)) hy]

lemma kA_insert_left {t : K} {x : ι → K} {S I : Finset ι} {a : ι} (ha : a ∉ S) (hI : I ⊆ S) :
    kA t x (insert a S) I = kA t x S I * ∏ i ∈ I, (t * x i - x a) / (x i - x a) := by
  unfold kA
  have haI : a ∉ I := fun h => ha (hI h)
  have : insert a S \ I = insert a (S \ I) := by
    ext j; simp only [mem_sdiff, mem_insert]; constructor
    · rintro ⟨h1 | h1, h2⟩ <;> simp_all
    · rintro (h1 | ⟨h1, h2⟩)
      · subst h1; exact ⟨Or.inl rfl, haI⟩
      · exact ⟨Or.inr h1, h2⟩
  rw [this, ← prod_mul_distrib]
  refine prod_congr rfl fun i hi => ?_
  rw [prod_insert (fun h => ha (mem_sdiff.1 h).1), mul_comm]

lemma kA_insert_insert {t : K} {x : ι → K} {S I : Finset ι} {a : ι} (ha : a ∉ S) (hI : I ⊆ S) :
    kA t x (insert a S) (insert a I) =
      (∏ j ∈ S \ I, (t * x a - x j) / (x a - x j)) * kA t x S I := by
  unfold kA
  have haI : a ∉ I := fun h => ha (hI h)
  have : insert a S \ insert a I = S \ I := by
    ext j; simp only [mem_sdiff, mem_insert]; constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (Or.inl h1) h2
      · exact ⟨h1, fun h => h2 (Or.inr h)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨Or.inr h1, ?_⟩
      rintro (h | h)
      · subst h; exact ha h1
      · exact h2 h
  rw [this, prod_insert haI]

lemma kB_insert_left {t : K} {x y : ι → K} {T I : Finset ι} {a : ι} (haI : a ∉ I) :
    kB t x y T (insert a I) =
      (∏ k ∈ T, (1 - x a * y k) / (1 - t * x a * y k)) * kB t x y T I := by
  unfold kB; rw [prod_insert haI]

lemma kB_insert_right {t : K} {x y : ι → K} {T I : Finset ι} {a : ι} (ha : a ∉ T) :
    kB t x y (insert a T) I =
      kB t x y T I * ∏ i ∈ I, (1 - x i * y a) / (1 - t * x i * y a) := by
  unfold kB
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i hi => ?_
  rw [prod_insert ha, mul_comm]

lemma kG_insert_succ {S T : Finset ι} {r : ℕ} {t : K} {x y : ι → K} {a : ι} (ha : a ∉ S) :
    kG (insert a S) T (r + 1) t x y =
      ∑ I ∈ S.powersetCard (r + 1),
          kA t x S I * kB t x y T I * ∏ i ∈ I, (t * x i - x a) / (x i - x a) +
        ∑ I ∈ S.powersetCard r, kA t x S I * kB t x y T I *
          ((∏ j ∈ S \ I, (t * x a - x j) / (x a - x j)) *
            ∏ k ∈ T, (1 - x a * y k) / (1 - t * x a * y k)) := by
  unfold kG
  rw [powersetCard_succ_insert ha, sum_union]
  · congr 1
    · refine sum_congr rfl fun I hI => ?_
      rw [kA_insert_left ha (mem_powersetCard.1 hI).1]; ring
    · rw [sum_image]
      · refine sum_congr rfl fun I hI => ?_
        have hIS := (mem_powersetCard.1 hI).1
        rw [kA_insert_insert ha hIS, kB_insert_left (fun h => ha (hIS h))]; ring
      · intro I hI J hJ hIJ
        have hI' : a ∉ I := fun h => ha ((mem_powersetCard.1 hI).1 h)
        have hJ' : a ∉ J := fun h => ha ((mem_powersetCard.1 hJ).1 h)
        simpa [hI', hJ'] using congrArg (fun s => s.erase a) hIJ
  · rw [disjoint_left]
    intro I hI hI2
    obtain ⟨J, -, rfl⟩ := mem_image.1 hI2
    exact ha ((mem_powersetCard.1 hI).1 (mem_insert_self a J))

lemma kG_insert_right {S T : Finset ι} {r : ℕ} {t : K} {x y : ι → K} {a : ι} (ha : a ∉ S) :
    kG T (insert a S) r t y x =
      ∑ J ∈ T.powersetCard r, kA t y T J * kB t y x S J *
        ∏ k ∈ J, (1 - y k * x a) / (1 - t * y k * x a) := by
  unfold kG
  refine sum_congr rfl fun J _ => ?_
  rw [kB_insert_right ha]; ring


lemma kG_reduce_left {S T : Finset ι} {r : ℕ} {t : K} {x y : ι → K} {a k : ι} (ha : a ∉ S)
    (hk : k ∈ T) (hak : x a * y k = 1) (h1 : ∀ i ∈ S, 1 - x i * y k ≠ 0)
    (h2 : ∀ i ∈ S, 1 - t * x i * y k ≠ 0) :
    kG (insert a S) T r t x y = kG S (T.erase k) r t x y := by
  rcases r with _ | r
  · rw [kG_zero, kG_zero]
  rw [kG_insert_succ ha]
  have hzero : ∑ I ∈ S.powersetCard r, kA t x S I * kB t x y T I *
      ((∏ j ∈ S \ I, (t * x a - x j) / (x a - x j)) *
        ∏ k ∈ T, (1 - x a * y k) / (1 - t * x a * y k)) = 0 := by
    refine sum_eq_zero fun I _ => ?_
    rw [prod_eq_zero hk (by rw [hak]; simp)]; simp
  rw [hzero, add_zero]
  unfold kG
  refine sum_congr rfl fun I hI => ?_
  have hIS := (mem_powersetCard.1 hI).1
  have hT : T = insert k (T.erase k) := (insert_erase hk).symm
  have hB : kB t x y T I =
      kB t x y (T.erase k) I * ∏ i ∈ I, (1 - x i * y k) / (1 - t * x i * y k) := by
    conv_lhs => rw [hT]
    exact kB_insert_right (notMem_erase k T)
  rw [hB, mul_assoc, mul_assoc, ← prod_mul_distrib]
  rw [prod_eq_one, mul_one]
  intro i hi
  have hiS := hIS hi
  have hxi : x i - x a ≠ 0 := by
    intro h
    apply h1 i hiS
    rw [sub_eq_zero.1 h, hak, sub_self]
  rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (h2 i hiS) hxi)]
  linear_combination (1 - t) * x i * hak

lemma kG_reduce_right {S T : Finset ι} {r : ℕ} {t : K} {x y : ι → K} {a k : ι} (ha : a ∉ S)
    (hk : k ∈ T) (hak : x a * y k = 1) (hy : ∀ l ∈ T, l ≠ k → y l ≠ y k)
    (hty : ∀ l ∈ T, y k ≠ t * y l) :
    kG T (insert a S) r t y x = kG (T.erase k) S r t y x := by
  rcases r with _ | r
  · rw [kG_zero, kG_zero]
  have hT : T = insert k (T.erase k) := (insert_erase hk).symm
  conv_lhs => rw [hT]
  rw [kG_insert_succ (notMem_erase k T)]
  have hzero : ∑ J ∈ (T.erase k).powersetCard r, kA t y (T.erase k) J * kB t y x (insert a S) J *
      ((∏ j ∈ T.erase k \ J, (t * y k - y j) / (y k - y j)) *
        ∏ i ∈ insert a S, (1 - y k * x i) / (1 - t * y k * x i)) = 0 := by
    refine sum_eq_zero fun J _ => ?_
    rw [prod_eq_zero (mem_insert_self a S) (by rw [mul_comm (y k), hak]; simp)]; simp
  rw [hzero, add_zero]
  unfold kG
  refine sum_congr rfl fun J hJ => ?_
  have hJT := (mem_powersetCard.1 hJ).1
  rw [kB_insert_right ha, mul_assoc, mul_assoc, ← prod_mul_distrib]
  rw [prod_eq_one, mul_one]
  intro l hl
  have hlT := hJT hl
  have hlk : l ≠ k := ne_of_mem_erase hlT
  have hlT' : l ∈ T := mem_of_mem_erase hlT
  have hyk : y k ≠ 0 := by
    intro h; apply hty k hk; rw [h, mul_zero]
  have hd1 : 1 - t * y l * x a ≠ 0 := by
    intro h
    apply hty l hlT'
    have : y k * (1 - t * y l * x a) = 0 := by rw [h, mul_zero]
    linear_combination this + t * y l * hak
  have hd2 : y l - y k ≠ 0 := sub_ne_zero.2 (hy l hlT' hlk)
  rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hd1 hd2)]
  linear_combination (1 - t) * y l * hak

/-- Genericity hypotheses used in the inductive proof. -/
def Hyp (S T : Finset ι) (t : K) (x y : ι → K) : Prop :=
  Set.InjOn x S ∧ Set.InjOn y T ∧ t ≠ 0 ∧ (∀ i ∈ S, ∀ k ∈ T, 1 - t * x i * y k ≠ 0) ∧
    (∀ i ∈ S, ∀ k ∈ T, 1 - x i * y k ≠ 0) ∧ (∀ k ∈ T, ∀ l ∈ T, y k ≠ t * y l)

omit [DecidableEq ι] in
lemma Hyp.mono {S T S' T' : Finset ι} {t : K} {x y : ι → K} (h : Hyp S T t x y) (hS : S' ⊆ S)
    (hT : T' ⊆ T) : Hyp S' T' t x y := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1.mono (by exact_mod_cast hS), h2.mono (by exact_mod_cast hT), h3,
    fun i hi k hk => h4 i (hS hi) k (hT hk), fun i hi k hk => h5 i (hS hi) k (hT hk),
    fun k hk l hl => h6 k (hT hk) l (hT hl)⟩


open Polynomial in
/-- The difference of the two sides as a function of the inserted variable, with denominators
cleared; it is a polynomial. -/
noncomputable def kP (S T : Finset ι) (r : ℕ) (t : K) (x y : ι → K) : K[X] :=
  ∑ I ∈ S.powersetCard (r + 1), C (kA t x S I * kB t x y T I) *
      ((∏ i ∈ I, (X - C (t * x i))) * (∏ j ∈ S \ I, (X - C (x j))) *
        ∏ k ∈ T, (1 - C (t * y k) * X)) +
    ∑ I ∈ S.powersetCard r, C (kA t x S I * kB t x y T I) *
      ((∏ j ∈ S \ I, (C t * X - C (x j))) * (∏ j ∈ I, (X - C (x j))) *
        ∏ k ∈ T, (1 - C (y k) * X)) -
    ∑ J ∈ T.powersetCard (r + 1), C (kA t y T J * kB t y x S J) *
      ((∏ k ∈ J, (1 - C (y k) * X)) * (∏ k ∈ T \ J, (1 - C (t * y k) * X)) *
        ∏ j ∈ S, (X - C (x j)))

lemma kP_congr {S T : Finset ι} {r : ℕ} {t : K} {x x' y : ι → K} (h : ∀ i ∈ S, x i = x' i) :
    kP S T r t x y = kP S T r t x' y := by
  unfold kP
  have hJ : ∀ J, kB t y x S J = kB t y x' S J := fun J => kB_congr (fun _ _ => rfl) h
  refine congrArg₂ (· - ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · refine sum_congr rfl fun I hI => ?_
    have hIS := (mem_powersetCard.1 hI).1
    rw [kA_congr h hIS, kB_congr (fun i hi => h i (hIS hi)) (fun _ _ => rfl)]
    congr 3
    · exact prod_congr rfl fun i hi => by rw [h i (hIS hi)]
    · exact prod_congr rfl fun j hj => by rw [h j (sdiff_subset hj)]
  · refine sum_congr rfl fun I hI => ?_
    have hIS := (mem_powersetCard.1 hI).1
    rw [kA_congr h hIS, kB_congr (fun i hi => h i (hIS hi)) (fun _ _ => rfl)]
    congr 3
    · exact prod_congr rfl fun j hj => by rw [h j (sdiff_subset hj)]
    · exact prod_congr rfl fun i hi => by rw [h i (hIS hi)]
  · refine sum_congr rfl fun J _ => ?_
    rw [hJ J]
    congr 2
    exact prod_congr rfl fun j hj => by rw [h j hj]

open Polynomial in
omit [DecidableEq ι] in
lemma natDegree_prod_le_card (s : Finset ι) (f : ι → K[X]) (h : ∀ i ∈ s, (f i).natDegree ≤ 1) :
    (∏ i ∈ s, f i).natDegree ≤ s.card :=
  (natDegree_prod_le s f).trans ((sum_le_sum h).trans (by simp))

open Polynomial in
lemma nd_lin1 (a b : K) : (C a * X - C b).natDegree ≤ 1 :=
  (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp))

open Polynomial in
lemma nd_lin2 (a : K) : (X - C a).natDegree ≤ 1 :=
  (natDegree_sub_le _ _).trans (max_le natDegree_X_le (by simp))

open Polynomial in
lemma nd_lin3 (a : K) : (1 - C a * X).natDegree ≤ 1 :=
  (natDegree_sub_le _ _).trans (max_le (by simp) ((natDegree_C_mul_le _ _).trans natDegree_X_le))

open Polynomial in
lemma kP_natDegree_le (S T : Finset ι) (r : ℕ) (t : K) (x y : ι → K) :
    (kP S T r t x y).natDegree ≤ S.card + T.card := by
  unfold kP
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · refine natDegree_sum_le_of_forall_le _ _ fun I hI => ?_
    have hIS := (mem_powersetCard.1 hI).1
    refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
    have h1 := natDegree_prod_le_card I (fun i => X - C (t * x i)) (fun _ _ => nd_lin2 _)
    have h2 := natDegree_prod_le_card (S \ I) (fun i => X - C (x i))
      (fun _ _ => nd_lin2 _)
    have h3 := natDegree_prod_le_card T (fun i => 1 - C (t * y i) * X)
      (fun _ _ => nd_lin3 _)
    have h4 := card_sdiff_add_card_eq_card hIS
    have h5 := (natDegree_mul_le (p := ∏ i ∈ I, (X - C (t * x i)))
      (q := ∏ j ∈ S \ I, (X - C (x j))))
    lia
  · refine natDegree_sum_le_of_forall_le _ _ fun I hI => ?_
    have hIS := (mem_powersetCard.1 hI).1
    refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
    have h1 := natDegree_prod_le_card (S \ I) (fun i => C t * X - C (x i))
      (fun _ _ => nd_lin1 _ _)
    have h2 := natDegree_prod_le_card I (fun i => X - C (x i)) (fun _ _ => nd_lin2 _)
    have h3 := natDegree_prod_le_card T (fun i => 1 - C (y i) * X)
      (fun _ _ => nd_lin3 _)
    have h4 := card_sdiff_add_card_eq_card hIS
    have h5 := (natDegree_mul_le (p := ∏ j ∈ S \ I, (C t * X - C (x j)))
      (q := ∏ j ∈ I, (X - C (x j))))
    lia
  · refine natDegree_sum_le_of_forall_le _ _ fun J hJ => ?_
    have hJT := (mem_powersetCard.1 hJ).1
    refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
    have h1 := natDegree_prod_le_card J (fun i => 1 - C (y i) * X)
      (fun _ _ => nd_lin3 _)
    have h2 := natDegree_prod_le_card (T \ J) (fun i => 1 - C (t * y i) * X)
      (fun _ _ => nd_lin3 _)
    have h3 := natDegree_prod_le_card S (fun i => X - C (x i)) (fun _ _ => nd_lin2 _)
    have h4 := card_sdiff_add_card_eq_card hJT
    have h5 := (natDegree_mul_le (p := ∏ k ∈ J, (1 - C (y k) * X))
      (q := ∏ k ∈ T \ J, (1 - C (t * y k) * X)))
    lia

omit [DecidableEq ι] in
lemma prod_eq_prod_mul_prod_div (s : Finset ι) (f g : ι → K) (h : ∀ i ∈ s, g i ≠ 0) :
    ∏ i ∈ s, f i = (∏ i ∈ s, g i) * ∏ i ∈ s, f i / g i := by
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun i hi => (mul_div_cancel₀ _ (h i hi)).symm

open Polynomial in
lemma kP_eval {S T : Finset ι} {r : ℕ} {t : K} {x y : ι → K} {a : ι} (ha : a ∉ S)
    (hc1 : ∀ j ∈ S, x a - x j ≠ 0) (hc2 : ∀ k ∈ T, 1 - t * y k * x a ≠ 0) :
    (kP S T r t x y).eval (x a) = ((∏ j ∈ S, (x a - x j)) * ∏ k ∈ T, (1 - t * y k * x a)) *
      (kG (insert a S) T (r + 1) t x y - kG T (insert a S) (r + 1) t y x) := by
  rw [kG_insert_succ ha, kG_insert_right ha]
  unfold kP
  simp only [eval_add, eval_sub, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_X, eval_one]
  rw [mul_sub, mul_add, mul_sum, mul_sum, mul_sum]
  congr 1
  · congr 1
    · refine sum_congr rfl fun I hI => ?_
      have hIS := (mem_powersetCard.1 hI).1
      have e1 : ∏ i ∈ I, (x a - t * x i) =
          (∏ i ∈ I, (x a - x i)) * ∏ i ∈ I, (t * x i - x a) / (x i - x a) := by
        rw [prod_eq_prod_mul_prod_div I _ (fun i => x a - x i) (fun i hi => hc1 i (hIS hi))]
        congr 1
        refine prod_congr rfl fun i hi => ?_
        rw [← neg_div_neg_eq]; congr 1 <;> ring
      rw [e1, ← prod_sdiff hIS]; ring
    · refine sum_congr rfl fun I hI => ?_
      have hIS := (mem_powersetCard.1 hI).1
      have e1 := prod_eq_prod_mul_prod_div (S \ I) (fun j => t * x a - x j) (fun j => x a - x j)
        (fun j hj => hc1 j (sdiff_subset hj))
      have e2 : ∏ k ∈ T, (1 - y k * x a) = (∏ k ∈ T, (1 - t * y k * x a)) *
          ∏ k ∈ T, (1 - x a * y k) / (1 - t * x a * y k) := by
        rw [prod_eq_prod_mul_prod_div T _ (fun k => 1 - t * y k * x a) hc2]
        congr 1
        exact prod_congr rfl fun k _ => by ring_nf
      rw [e1, e2, ← prod_sdiff hIS]; ring
  · refine sum_congr rfl fun J hJ => ?_
    have hJT := (mem_powersetCard.1 hJ).1
    have e1 := prod_eq_prod_mul_prod_div J (fun k => 1 - y k * x a) (fun k => 1 - t * y k * x a)
      (fun k hk => hc2 k (hJT hk))
    rw [e1, ← prod_sdiff hJT]; ring


lemma insert_sdiff_insert_of_notMem {S I : Finset ι} {a : ι} (ha : a ∉ S) :
    insert a S \ insert a I = S \ I := by
  ext j; simp only [mem_sdiff, mem_insert]; constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd (Or.inl h1) h2
    · exact ⟨h1, fun h => h2 (Or.inr h)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨Or.inr h1, ?_⟩
    rintro (h | h)
    · subst h; exact ha h1
    · exact h2 h

omit [DecidableEq ι] in
lemma prod_pow_inv_aux (I : Finset ι) (f g : ι → K) (c : K) (h : ∀ i ∈ I, f i = c * g i) :
    ∏ i ∈ I, f i = c ^ I.card * ∏ i ∈ I, g i := by
  rw [prod_congr rfl h, prod_mul_distrib, prod_const]

lemma kaux1 (t a b : K) (ht : t ≠ 0) (hb : b ≠ 0) (h : 1 - t * a * b ≠ 0) :
    (1 - a * b) / (1 - t * a * b) * ((t * b)⁻¹ - a) = t⁻¹ * (t * (t * b)⁻¹ - a) := by
  rw [div_mul_eq_mul_div, div_eq_iff h]
  field_simp

lemma kaux2 (t a b : K) (ht : t ≠ 0) (hb : b ≠ 0) (h : 1 - t * b * a ≠ 0) :
    (1 - b * a) / (1 - t * b * a) * ((t * b)⁻¹ - a) = t⁻¹ * (t * (t * b)⁻¹ - a) := by
  rw [div_mul_eq_mul_div, div_eq_iff h]
  field_simp

lemma kaux3 (t a b : K) (ht : t ≠ 0) (hb : b ≠ 0) (h : b - a ≠ 0) :
    (t * b - a) / (b - a) * (1 - t * a * (t * b)⁻¹) = t * (1 - a * (t * b)⁻¹) := by
  rw [div_mul_eq_mul_div, div_eq_iff h]
  field_simp

open Polynomial in
lemma kP_eval_w {S T' : Finset ι} {r : ℕ} {t : K} {x y : ι → K} {k : ι} (hk : k ∉ T')
    (ht : t ≠ 0) (hyk : y k ≠ 0) (hS : ∀ i ∈ S, 1 - t * x i * y k ≠ 0)
    (hT : ∀ m ∈ T', y k - y m ≠ 0) (hcard : T'.card = S.card) :
    (kP S (insert k T') r t x y).eval (t * y k)⁻¹ =
      (∏ j ∈ S, (t * (t * y k)⁻¹ - x j)) * (∏ l ∈ insert k T', (1 - y l * (t * y k)⁻¹)) *
        (t⁻¹) ^ r * (kG S T' r t x y - kG T' S r t y x) := by
  have hwk : t * y k * (t * y k)⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero ht hyk)
  unfold kP
  simp only [eval_add, eval_sub, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_X, eval_one]
  have hfirst : ∑ I ∈ S.powersetCard (r + 1), kA t x S I * kB t x y (insert k T') I *
      ((∏ i ∈ I, ((t * y k)⁻¹ - t * x i)) * (∏ j ∈ S \ I, ((t * y k)⁻¹ - x j)) *
        ∏ l ∈ insert k T', (1 - t * y l * (t * y k)⁻¹)) = 0 := by
    refine sum_eq_zero fun I _ => ?_
    rw [prod_eq_zero (mem_insert_self k T') (by rw [hwk, sub_self]), mul_zero, mul_zero]
  rw [hfirst, zero_add, mul_sub]
  congr 1
  · -- the residue of the left-hand side
    unfold kG
    rw [mul_sum]
    refine sum_congr rfl fun I hI => ?_
    obtain ⟨hIS, hIc⟩ := mem_powersetCard.1 hI
    rw [kB_insert_right hk]
    have key : (∏ i ∈ I, (1 - x i * y k) / (1 - t * x i * y k)) *
        ∏ i ∈ I, ((t * y k)⁻¹ - x i) = (t⁻¹) ^ r * ∏ i ∈ I, (t * (t * y k)⁻¹ - x i) := by
      rw [← prod_mul_distrib, ← hIc]
      refine prod_pow_inv_aux I _ _ _ fun i hi => ?_
      exact kaux1 t (x i) (y k) ht hyk (hS i (hIS hi))
    rw [← prod_sdiff hIS]
    linear_combination (kA t x S I * kB t x y T' I * (∏ j ∈ S \ I, (t * (t * y k)⁻¹ - x j)) *
      ∏ l ∈ insert k T', (1 - y l * (t * y k)⁻¹)) * key
  · -- the residue of the right-hand side
    unfold kG
    rw [mul_sum, powersetCard_succ_insert hk, sum_union]
    · have hz : ∑ J ∈ T'.powersetCard (r + 1), kA t y (insert k T') J * kB t y x S J *
          ((∏ l ∈ J, (1 - y l * (t * y k)⁻¹)) *
            (∏ l ∈ insert k T' \ J, (1 - t * y l * (t * y k)⁻¹)) *
            ∏ j ∈ S, ((t * y k)⁻¹ - x j)) = 0 := by
        refine sum_eq_zero fun J hJ => ?_
        have hkJ : k ∉ J := fun h => hk ((mem_powersetCard.1 hJ).1 h)
        rw [prod_eq_zero (mem_sdiff.2 ⟨mem_insert_self k T', hkJ⟩) (by rw [hwk, sub_self])]
        simp
      rw [hz, zero_add, sum_image]
      · refine sum_congr rfl fun J hJ => ?_
        obtain ⟨hJT, hJc⟩ := mem_powersetCard.1 hJ
        have hkJ : k ∉ J := fun h => hk (hJT h)
        rw [kA_insert_insert hk hJT, kB_insert_left hkJ, prod_insert hkJ,
          insert_sdiff_insert_of_notMem hk, prod_insert hk, ← prod_sdiff hJT]
        have keyA : (∏ m ∈ T' \ J, (t * y k - y m) / (y k - y m)) *
            ∏ m ∈ T' \ J, (1 - t * y m * (t * y k)⁻¹) =
              t ^ (T' \ J).card * ∏ m ∈ T' \ J, (1 - y m * (t * y k)⁻¹) := by
          rw [← prod_mul_distrib]
          refine prod_pow_inv_aux _ _ _ _ fun m hm => ?_
          exact kaux3 t (y m) (y k) ht hyk (hT m (sdiff_subset hm))
        have keyB : (∏ i ∈ S, (1 - y k * x i) / (1 - t * y k * x i)) *
            ∏ i ∈ S, ((t * y k)⁻¹ - x i) = (t⁻¹) ^ S.card * ∏ i ∈ S, (t * (t * y k)⁻¹ - x i) := by
          rw [← prod_mul_distrib]
          refine prod_pow_inv_aux _ _ _ _ fun i hi => ?_
          have : 1 - t * y k * x i ≠ 0 := by
            have := hS i hi; contrapose! this; linear_combination this
          exact kaux2 t (x i) (y k) ht hyk this
        have hpow : t ^ (T' \ J).card * (t⁻¹) ^ S.card = (t⁻¹) ^ r := by
          have hc : S.card = (T' \ J).card + r := by
            rw [← hcard, ← hJc, card_sdiff_add_card_eq_card hJT]
          rw [hc, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ ht, one_pow, one_mul]
        linear_combination (kA t y T' J * kB t y x S J * (1 - y k * (t * y k)⁻¹) *
            ∏ l ∈ J, (1 - y l * (t * y k)⁻¹)) *
          ((∏ i ∈ S, (1 - y k * x i) / (1 - t * y k * x i)) * (∏ i ∈ S, ((t * y k)⁻¹ - x i)) *
              keyA +
            t ^ (T' \ J).card * (∏ m ∈ T' \ J, (1 - y m * (t * y k)⁻¹)) * keyB +
            (∏ m ∈ T' \ J, (1 - y m * (t * y k)⁻¹)) * (∏ i ∈ S, (t * (t * y k)⁻¹ - x i)) * hpow)
      · intro I hI J hJ hIJ
        have hI' : k ∉ I := fun h => hk ((mem_powersetCard.1 hI).1 h)
        have hJ' : k ∉ J := fun h => hk ((mem_powersetCard.1 hJ).1 h)
        simpa [hI', hJ'] using congrArg (fun s => s.erase k) hIJ
    · rw [disjoint_left]
      intro I hI hI2
      obtain ⟨J, -, rfl⟩ := mem_image.1 hI2
      exact hk ((mem_powersetCard.1 hI).1 (mem_insert_self k J))


/-- The kernel identity for finite index sets of equal size under the genericity hypotheses
`Hyp`, proved by induction on the size. -/
theorem kG_symm (t : K) : ∀ (n : ℕ) (S T : Finset ι), S.card = n → T.card = n →
    ∀ (r : ℕ) (x y : ι → K), Hyp S T t x y → kG S T r t x y = kG T S r t y x := by
  classical
  intro n
  induction n with
  | zero =>
    intro S T hS hT r x y _
    rw [card_eq_zero.1 hS, card_eq_zero.1 hT]
    rcases r with _ | r
    · rw [kG_zero, kG_zero]
    · rw [kG_empty_succ, kG_empty_succ]
  | succ n ih =>
    intro S T hS hT r x y hH
    obtain ⟨a, haS⟩ : S.Nonempty := card_pos.1 (by lia)
    obtain ⟨S', haS', rfl⟩ : ∃ S', a ∉ S' ∧ S = insert a S' :=
      ⟨S.erase a, notMem_erase a S, (insert_erase haS).symm⟩
    have hS' : S'.card = n := by rw [card_insert_of_notMem haS'] at hS; lia
    rcases r with _ | r
    · rw [kG_zero, kG_zero]
    have hH0 := hH
    obtain ⟨hinjx, hinjy, ht, h1, h2, h3⟩ := hH
    have hyne : ∀ k ∈ T, y k ≠ 0 := fun k hk h => h3 k hk k hk (by rw [h, mul_zero])
    have hcardE : ∀ k ∈ T, (T.erase k).card = n := fun k hk => by
      rw [card_erase_of_mem hk]; lia
    have hsub : S' ⊆ insert a S' := subset_insert a S'
    have hP : kP S' T r t x y = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
        (T.image (fun k => (y k)⁻¹) ∪ T.image (fun k => (t * y k)⁻¹))
      · intro c hc
        rcases mem_union.1 hc with hc | hc
        · obtain ⟨k, hk, rfl⟩ := mem_image.1 hc
          set x' := Function.update x a (y k)⁻¹ with hx'
          have hx'S : ∀ i ∈ S', x i = x' i := fun i hi =>
            (Function.update_of_ne (by rintro rfl; exact haS' hi) _ _).symm
          have hx'a : x' a = (y k)⁻¹ := Function.update_self _ _ _
          have hc1 : ∀ j ∈ S', x' a - x' j ≠ 0 := by
            intro j hj h
            rw [hx'a, ← hx'S j hj] at h
            apply h2 j (mem_insert_of_mem hj) k hk
            rw [← sub_eq_zero.1 h, inv_mul_cancel₀ (hyne k hk), sub_self]
          have hc2 : ∀ l ∈ T, 1 - t * y l * x' a ≠ 0 := by
            intro l hl h
            rw [hx'a] at h
            apply h3 k hk l hl
            have := congrArg (· * y k) h
            simp only [zero_mul, sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ (hyne k hk),
              mul_one] at this
            exact sub_eq_zero.1 this
          have hak : x' a * y k = 1 := by rw [hx'a, inv_mul_cancel₀ (hyne k hk)]
          rw [kP_congr hx'S, ← hx'a, kP_eval haS' hc1 hc2,
            kG_reduce_left haS' hk hak
              (fun i hi => by rw [← hx'S i hi]; exact h2 i (hsub hi) k hk)
              (fun i hi => by rw [← hx'S i hi]; exact h1 i (hsub hi) k hk),
            kG_reduce_right haS' hk hak (fun l hl hlk h => hlk (hinjy hl hk h)) (h3 k hk)]
          have e1 : kG S' (T.erase k) (r + 1) t x' y = kG S' (T.erase k) (r + 1) t x y :=
            kG_congr (fun i hi => (hx'S i hi).symm) (fun _ _ => rfl)
          have e2 : kG (T.erase k) S' (r + 1) t y x' = kG (T.erase k) S' (r + 1) t y x :=
            kG_congr (fun _ _ => rfl) (fun i hi => (hx'S i hi).symm)
          rw [e1, e2, ih S' (T.erase k) hS' (hcardE k hk) (r + 1) x y
            (hH0.mono hsub (erase_subset k T)), sub_self, mul_zero]
        · obtain ⟨k, hk, rfl⟩ := mem_image.1 hc
          have hw := kP_eval_w (S := S') (T' := T.erase k) (r := r) (x := x) (y := y)
            (notMem_erase k T) ht (hyne k hk) (fun i hi => h1 i (hsub hi) k hk)
            (fun m hm => sub_ne_zero.2 fun h =>
              (ne_of_mem_erase hm) (hinjy (mem_of_mem_erase hm) hk h.symm))
            (by rw [hcardE k hk, hS'])
          rw [insert_erase hk] at hw
          rw [hw, ih S' (T.erase k) hS' (hcardE k hk) r x y (hH0.mono hsub (erase_subset k T)),
            sub_self, mul_zero]
      · have hdeg := kP_natDegree_le S' T r t x y
        rw [card_union_of_disjoint, card_image_of_injOn, card_image_of_injOn]
        · lia
        · intro k hk l hl h
          exact hinjy hk hl (mul_left_cancel₀ ht (inv_inj.1 h))
        · intro k hk l hl h
          exact hinjy hk hl (inv_inj.1 h)
        · rw [disjoint_left]
          intro c hc hc'
          obtain ⟨k, hk, rfl⟩ := mem_image.1 hc
          obtain ⟨l, hl, hkl⟩ := mem_image.1 hc'
          exact h3 k hk l hl (inv_inj.1 hkl).symm
    have hc1 : ∀ j ∈ S', x a - x j ≠ 0 := fun j hj h =>
      haS' ((hinjx (mem_insert_self a S') (hsub hj) (sub_eq_zero.1 h)) ▸ hj)
    have hc2 : ∀ k ∈ T, 1 - t * y k * x a ≠ 0 := by
      intro k hk h
      apply h1 a (mem_insert_self a S') k hk
      linear_combination h
    have hev := kP_eval (r := r) (t := t) (x := x) (y := y) (T := T) haS' hc1 hc2
    rw [hP, Polynomial.eval_zero] at hev
    have hC : (∏ j ∈ S', (x a - x j)) * ∏ k ∈ T, (1 - t * y k * x a) ≠ 0 :=
      mul_ne_zero (prod_ne_zero_iff.2 hc1) (prod_ne_zero_iff.2 hc2)
    exact sub_eq_zero.1 ((mul_eq_zero.1 hev.symm).resolve_left hC)


/-! ### Transfer from the generic point to an arbitrary point -/

/-- `kernelSum` written with `Ring.inverse`, so that it makes sense in any commutative ring. -/
noncomputable def kSR {A : Type*} [CommRing A] (N r : ℕ) (t : A) (x y : Fin N → A) : A :=
  ∑ I ∈ (univ : Finset (Fin N)).powersetCard r,
    (∏ i ∈ I, ∏ j ∈ univ \ I, (t * x i - x j) * Ring.inverse (x i - x j)) *
      ∏ i ∈ I, ∏ j, (1 - x i * y j) * Ring.inverse (1 - t * x i * y j)

lemma kSR_eq_kernelSum {L : Type*} [Field L] (N r : ℕ) (t : L) (x y : Fin N → L) :
    kSR N r t x y = kernelSum N r t x y := by
  simp only [kSR, kernelSum, Ring.inverse_eq_inv', div_eq_mul_inv]

lemma map_ringInverse_of_isUnit {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {u : A}
    (hu : IsUnit u) : f (Ring.inverse u) = Ring.inverse (f u) := by
  obtain ⟨u, rfl⟩ := hu
  have h : f ↑u⁻¹ = ↑(Units.map (f : A →* B) u)⁻¹ := (Units.coe_map_inv _ u).symm
  rw [Ring.inverse_unit, h, ← Ring.inverse_unit]
  rfl

lemma map_kSR {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (N r : ℕ) (t : A)
    (x y : Fin N → A) (hx : ∀ i j, i ≠ j → IsUnit (x i - x j))
    (hxy : ∀ i j, IsUnit (1 - t * x i * y j)) :
    f (kSR N r t x y) = kSR N r (f t) (f ∘ x) (f ∘ y) := by
  unfold kSR
  simp only [map_sum, map_mul, map_prod]
  refine sum_congr rfl fun I _ => ?_
  congr 1
  · refine prod_congr rfl fun i hi => prod_congr rfl fun j hj => ?_
    have hij : i ≠ j := fun h => (mem_sdiff.1 hj).2 (h ▸ hi)
    rw [map_ringInverse_of_isUnit f (hx i j hij)]
    simp
  · refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
    rw [map_ringInverse_of_isUnit f (hxy i j)]
    simp

section Generic

open MvPolynomial

variable (N : ℕ)

/-- The generic point: the variables of the polynomial ring `ℤ[t, x_i, y_j]`. -/
abbrev GV := Option (Fin N ⊕ Fin N)

lemma mvpoly_ne_zero_of_eval {σ : Type*} (p : MvPolynomial σ ℤ) (f : σ → ℤ)
    (h : MvPolynomial.eval f p ≠ 0) : p ≠ 0 := fun hp => h (by rw [hp, map_zero])

lemma generic_hyp :
    Hyp (univ : Finset (Fin N)) univ
      (algebraMap (MvPolynomial (GV N) ℤ) (FractionRing (MvPolynomial (GV N) ℤ)) (X none))
      (fun i => algebraMap (MvPolynomial (GV N) ℤ) (FractionRing (MvPolynomial (GV N) ℤ))
        (X (some (Sum.inl i))))
      (fun j => algebraMap (MvPolynomial (GV N) ℤ) (FractionRing (MvPolynomial (GV N) ℤ))
        (X (some (Sum.inr j)))) := by
  set R := MvPolynomial (GV N) ℤ
  set F := FractionRing R
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hne : ∀ p : R, p ≠ 0 → algebraMap R F p ≠ 0 := fun p hp =>
    (map_ne_zero_iff _ hinj).2 hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _ j _ h
    have := X_injective (hinj h)
    simpa using this
  · intro i _ j _ h
    have := X_injective (hinj h)
    simpa using this
  · exact hne _ (X_ne_zero _)
  · intro i _ k _
    have := hne (1 - X none * X (some (Sum.inl i)) * X (some (Sum.inr k)))
      (mvpoly_ne_zero_of_eval _ (fun _ => 0) (by simp))
    simpa using this
  · intro i _ k _
    have := hne (1 - X (some (Sum.inl i)) * X (some (Sum.inr k)))
      (mvpoly_ne_zero_of_eval _ (fun _ => 0) (by simp))
    simpa using this
  · intro k _ l _ h
    have := hne (X (some (Sum.inr k)) - X none * X (some (Sum.inr l)))
      (mvpoly_ne_zero_of_eval _ (fun v => if v = none then 2 else 1) (by simp))
    apply this
    simp only [map_sub, map_mul]
    exact sub_eq_zero.2 h

lemma generic_kernelSum_comm (r : ℕ) :
    kernelSum N r
      (algebraMap (MvPolynomial (GV N) ℤ) (FractionRing (MvPolynomial (GV N) ℤ)) (X none))
      (fun i => algebraMap (MvPolynomial (GV N) ℤ) (FractionRing (MvPolynomial (GV N) ℤ))
        (X (some (Sum.inl i))))
      (fun j => algebraMap (MvPolynomial (GV N) ℤ) (FractionRing (MvPolynomial (GV N) ℤ))
        (X (some (Sum.inr j)))) =
    kernelSum N r
      (algebraMap (MvPolynomial (GV N) ℤ) (FractionRing (MvPolynomial (GV N) ℤ)) (X none))
      (fun j => algebraMap (MvPolynomial (GV N) ℤ) (FractionRing (MvPolynomial (GV N) ℤ))
        (X (some (Sum.inr j))))
      (fun i => algebraMap (MvPolynomial (GV N) ℤ) (FractionRing (MvPolynomial (GV N) ℤ))
        (X (some (Sum.inl i)))) := by
  rw [kernelSum_eq_kG, kernelSum_eq_kG]
  exact kG_symm _ N univ univ (card_fin N) (card_fin N) r _ _ (generic_hyp N)

theorem kernelSum_comm_aux {L : Type*} [Field L] (r : ℕ) (t : L) (x y : Fin N → L)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j, 1 - t * x i * y j ≠ 0) :
    kernelSum N r t x y = kernelSum N r t y x := by
  set R := MvPolynomial (GV N) ℤ
  set F := FractionRing R
  let ev : R →+* L := eval₂Hom (Int.castRingHom L) (fun v => Option.elim v t (Sum.elim x y))
  let M : Submonoid R := Submonoid.comap ev (nonZeroDivisors L)
  have hM : ∀ p : R, p ∈ M ↔ ev p ≠ 0 := fun p => mem_nonZeroDivisors_iff_ne_zero
  let A := Localization M
  have hχ : ∀ s : M, IsUnit (ev s) := fun s => IsUnit.mk0 _ ((hM s).1 s.2)
  have hRF : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hψ : ∀ s : M, IsUnit (algebraMap R F s) := fun s =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ hRF).2 fun h => (hM s).1 s.2 (by rw [h, map_zero]))
  let χ : A →+* L := IsLocalization.lift hχ
  let ψ : A →+* F := IsLocalization.lift hψ
  have hMle : M ≤ nonZeroDivisors R := fun p hp =>
    mem_nonZeroDivisors_of_ne_zero fun h => (hM p).1 hp (by rw [h, map_zero])
  have hψinj : Function.Injective ψ := by
    rw [IsLocalization.lift_injective_iff]
    intro a b
    constructor
    · intro h; rw [IsLocalization.injective A hMle h]
    · intro h; rw [hRF h]
  let gt : R := X none
  let gx : Fin N → R := fun i => X (some (Sum.inl i))
  let gy : Fin N → R := fun j => X (some (Sum.inr j))
  have evt : ev gt = t := eval₂Hom_X' _ _ _
  have evx : ∀ i, ev (gx i) = x i := fun i => eval₂Hom_X' _ _ _
  have evy : ∀ j, ev (gy j) = y j := fun j => eval₂Hom_X' _ _ _
  have hunit : ∀ p : R, ev p ≠ 0 → IsUnit (algebraMap R A p) := fun p hp =>
    IsLocalization.map_units A (⟨p, (hM p).2 hp⟩ : M)
  let at' : A := algebraMap R A gt
  let ax : Fin N → A := fun i => algebraMap R A (gx i)
  let ay : Fin N → A := fun j => algebraMap R A (gy j)
  have hux : ∀ i j, i ≠ j → IsUnit (ax i - ax j) := fun i j hij => by
    have := hunit (gx i - gx j) (by rw [map_sub, evx, evx]; exact sub_ne_zero.2 (hx.ne hij))
    simpa [ax] using this
  have huy : ∀ i j, i ≠ j → IsUnit (ay i - ay j) := fun i j hij => by
    have := hunit (gy i - gy j) (by rw [map_sub, evy, evy]; exact sub_ne_zero.2 (hy.ne hij))
    simpa [ay] using this
  have huxy : ∀ i j, IsUnit (1 - at' * ax i * ay j) := fun i j => by
    have := hunit (1 - gt * gx i * gy j) (by simpa [evt, evx, evy] using hxy i j)
    simpa [at', ax, ay] using this
  have huyx : ∀ i j, IsUnit (1 - at' * ay i * ax j) := fun i j => by
    have := hunit (1 - gt * gy i * gx j) (by
      have := hxy j i
      simp only [map_sub, map_mul, map_one, evt, evx, evy]
      contrapose! this; linear_combination this)
    simpa [at', ax, ay] using this
  have hψt : ψ at' = algebraMap R F gt := IsLocalization.lift_eq hψ _
  have hψx : ψ ∘ ax = fun i => algebraMap R F (gx i) := funext fun i => IsLocalization.lift_eq hψ _
  have hψy : ψ ∘ ay = fun i => algebraMap R F (gy i) := funext fun i => IsLocalization.lift_eq hψ _
  have hχt : χ at' = t := (IsLocalization.lift_eq hχ _).trans evt
  have hχx : χ ∘ ax = x := funext fun i => (IsLocalization.lift_eq hχ _).trans (evx i)
  have hχy : χ ∘ ay = y := funext fun i => (IsLocalization.lift_eq hχ _).trans (evy i)
  have key : kSR N r at' ax ay = kSR N r at' ay ax := by
    apply hψinj
    rw [map_kSR ψ N r _ _ _ hux huxy, map_kSR ψ N r _ _ _ huy huyx, hψt, hψx, hψy,
      kSR_eq_kernelSum, kSR_eq_kernelSum]
    exact generic_kernelSum_comm N r
  have := congrArg χ key
  rwa [map_kSR χ N r _ _ _ hux huxy, map_kSR χ N r _ _ _ huy huyx, hχt, hχx, hχy,
    kSR_eq_kernelSum, kSR_eq_kernelSum] at this

end Generic

end KernelSymm

/-- Macdonald's kernel identity (Symmetric Functions and Hall Polynomials, Ch. VI, §3):
the sum is symmetric under exchanging the two alphabets. -/
theorem kernelSum_comm {K : Type*} [Field K] (N r : ℕ) (t : K) (x y : Fin N → K)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j, 1 - t * x i * y j ≠ 0) :
    kernelSum N r t x y = kernelSum N r t y x := by
  exact KernelSymm.kernelSum_comm_aux N r t x y hx hy hxy

end Macdonald
