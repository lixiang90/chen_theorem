import ChenTheorem.Lemma9.LinearSieve.BuchstabFirstTerm
import ChenTheorem.Lemma9.LinearSieve.RosserDepthRecursion

open Finset Filter
open scoped Classical

namespace Chen.LinearSieve

/-- Exact propagation of an additive child error. The multiplier is the
actual Buchstab tail mass, not the number of primes in the interval. -/
theorem rosserStoppingMass_step_of_child_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (n z m : ℕ) (hmz : m ≤ z) (upper : Bool) (D E : ℝ) (H : ℕ → ℝ)
    (hactive : ¬(upper = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2))
    (hchild : ∀ p ∈ Ioc m z, p ∈ P →
      rosserRelativeStoppingMass P n p (!upper) (D / p) ≤ H p + E) :
    rosserRelativeStoppingMass P (n + 1) (z + 1) upper D ≤
      rosserStoppingPrefix P n z upper D m +
        (∑ p ∈ Ioc m z, H p * buchstabCoefficient P z p) +
          E * (sieveProduct P primeDensity (m + 1) /
            sieveProduct P primeDensity (z + 1) - 1) := by
  rw [rosserRelativeStoppingMass_split P hP hodd n z m hmz upper D hactive]
  have hsum : (∑ p ∈ Ioc m z, buchstabCoefficient P z p *
      rosserRelativeStoppingMass P n p (!upper) (D / p)) ≤
      ∑ p ∈ Ioc m z, (H p + E) * buchstabCoefficient P z p := by
    apply sum_le_sum
    intro p hp
    by_cases hpP : p ∈ P
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hchild p hp hpP)
        (normalized_buchstab_mass_nonneg P hP hodd (z + 1) p)
    · simp [buchstabCoefficient, hpP]
  have hmass : (∑ p ∈ Ioc m z, buchstabCoefficient P z p) =
      sieveProduct P primeDensity (m + 1) / sieveProduct P primeDensity (z + 1) - 1 :=
    sum_normalized_buchstab_mass P hP hodd m z hmz
  simp_rw [add_mul] at hsum
  rw [sum_add_distrib, ← mul_sum, hmass] at hsum
  linarith

/-- A concrete depth step with continuous main term and explicit additive
error propagation. The small-prime prefix vanishes under a power condition. -/
theorem rosserStoppingMass_continuous_step :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, ∀ D w E : ℝ, ∀ z : ℕ,
      1 < D → 2 ≤ w → w ≤ z → rosserContinuousCutoff (n + 2) ≤ sieveParameter D z →
      (⌊w⌋₊ : ℝ) ^ (n + 4) < D →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ upper : Bool, (¬(upper = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2)) →
      (∀ p ∈ Ioc ⌊w⌋₊ z, p ∈ P →
        rosserRelativeStoppingMass P (n + 1) p (!upper) (D / p) ≤
          rosserContinuousTerm (n + 1) (sieveParameter D p - 1) + E) →
      rosserRelativeStoppingMass P (n + 2) (z + 1) upper D ≤
        rosserContinuousTerm (n + 2) (sieveParameter D z) +
          2 * K * rosserContinuousTerm (n + 1) (sieveParameter D z - 1) / Real.log w +
          E * (sieveProduct P primeDensity (⌊w⌋₊ + 1) /
            sieveProduct P primeDensity (z + 1) - 1) := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_allContinuousTerms_bound
  refine ⟨K, hK, ?_⟩
  intro n D w E z hD hw hwz hs hpower P hP hodd upper hactive hchild
  have hmz : ⌊w⌋₊ ≤ z := (Nat.floor_le_floor hwz).trans_eq (Nat.floor_natCast z)
  have h := rosserStoppingMass_step_of_child_bound P hP hodd (n + 1) z ⌊w⌋₊ hmz
    upper D E (fun p => rosserContinuousTerm (n + 1) (sieveParameter D p - 1)) hactive hchild
  rw [rosserStoppingPrefix_eq_zero_of_power_level P hP (n + 1) z upper D ⌊w⌋₊ hpower,
    zero_add] at h
  exact h.trans (_root_.add_le_add (hb n D w z hD hw hwz hs P hP hodd) le_rfl)

end Chen.LinearSieve
