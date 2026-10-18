import PartitionDivision

/-!
# Solution: bridge from `Challenge` to the PartitionDivision library

Each definition below unfolds to the library definition with the same body, and each theorem is
the corresponding library theorem.
-/

noncomputable section

open Finset

namespace Comparator

section Definitions

variable (σ) (R : Type*) [CommSemiring R]

/-- See `PartitionDivision.esymmSeries`. -/
def esymmSeries (r : ℕ) : MvPowerSeries σ R := PartitionDivision.esymmSeries σ R r

/-- See `PartitionDivision.esymmSeriesPart`. -/
def esymmSeriesPart {n : ℕ} (mu : n.Partition) : MvPowerSeries σ R :=
  PartitionDivision.esymmSeriesPart σ R mu

/-- See `PartitionDivision.msymmSeries`. -/
def msymmSeries {n : ℕ} (lam : n.Partition) : MvPowerSeries σ R :=
  PartitionDivision.msymmSeries σ R lam

/-- See `PartitionDivision.partitionDivision`. -/
def partitionDivision (k : ℕ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R :=
  PartitionDivision.partitionDivision σ R k

end Definitions

theorem partitionDivision_msymmSeries {σ R : Type*} [CommSemiring R] {k m n : ℕ}
    (hk : 0 < k) (lam : n.Partition) (nu : m.Partition) (h : lam.parts = nu.parts.map (k * ·)) :
    partitionDivision σ R k (msymmSeries σ R lam) = msymmSeries σ R nu :=
  PartitionDivision.partitionDivision_msymmSeries hk lam nu h

theorem partitionDivision_msymmSeries_eq_zero {σ R : Type*} [CommSemiring R] {k n : ℕ}
    (hk : 0 < k) (lam : n.Partition) (h : ∃ p ∈ lam.parts, ¬ k ∣ p) :
    partitionDivision σ R k (msymmSeries σ R lam) = 0 :=
  PartitionDivision.partitionDivision_msymmSeries_eq_zero hk lam h

theorem partitionDivision_ePositive {k n : ℕ} (hk : 0 < k)
    (mu : (k * n).Partition) :
    ∃ c : n.Partition → ℕ,
      partitionDivision ℕ ℤ k (esymmSeriesPart ℕ ℤ mu) =
        ∑ nu, (c nu : ℤ) • esymmSeriesPart ℕ ℤ nu :=
  PartitionDivision.partitionDivision_ePositive hk mu

theorem partitionDivision_ePositive_finite {N k n : ℕ} (hk : 0 < k) (hn : n ≤ N)
    (mu : (k * n).Partition) :
    ∃ c : n.Partition → ℕ, ∀ d : Fin N →₀ ℕ,
      (∑ nu, c nu • MvPolynomial.esymmPart (Fin N) ℤ nu).coeff d =
        (MvPolynomial.esymmPart (Fin N) ℤ mu).coeff (k • d) := by
  obtain ⟨c, hc⟩ :=
    PartitionDivision.exponentDiv_esymmPart_ePositive (N := N) hk hn mu
  exact ⟨c, fun d ↦ by rw [← hc, PartitionDivision.coeff_exponentDiv hk]⟩

end Comparator
