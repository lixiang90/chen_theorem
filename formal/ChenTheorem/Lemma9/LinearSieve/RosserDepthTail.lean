import ChenTheorem.Lemma9.LinearSieve.RosserChainBound
import Mathlib.Analysis.Complex.Exponential

open Finset

namespace Chen.LinearSieve

theorem pow_div_factorial_add_le (x : ℝ) (hx : 0 ≤ x) (N k : ℕ) :
    x ^ (N + k) / (N + k).factorial ≤ (x ^ N / N.factorial) * (x ^ k / k.factorial) := by
  have hfac : (N.factorial : ℝ) * k.factorial ≤ (N + k).factorial := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (N + k))
      (Nat.factorial_mul_factorial_dvd_factorial_add N k)
  have hpos : (0 : ℝ) < (N.factorial : ℝ) * k.factorial := by positivity
  calc
    _ ≤ x ^ (N + k) / ((N.factorial : ℝ) * k.factorial) :=
      div_le_div_of_nonneg_left (pow_nonneg hx _) hpos hfac
    _ = _ := by rw [pow_add]; ring

/-- A finite exponential-series tail, with constants retained exactly. -/
theorem sum_Ico_pow_div_factorial_le (x : ℝ) (hx : 0 ≤ x) (N M : ℕ) :
    (∑ n ∈ Ico N M, x ^ n / n.factorial) ≤ (x ^ N / N.factorial) * Real.exp x := by
  rw [sum_Ico_eq_sum_range]
  calc
    _ ≤ ∑ k ∈ range (M - N), (x ^ N / N.factorial) * (x ^ k / k.factorial) := by
      apply sum_le_sum
      intro k _
      simpa only [Nat.add_comm] using pow_div_factorial_add_le x hx N k
    _ = (x ^ N / N.factorial) * ∑ k ∈ range (M - N), x ^ k / k.factorial := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hx (M - N)) (by positivity)

/-- Total density mass below the exclusive prime cutoff. -/
noncomputable def primeDensityMass (P : Finset ℕ) (z : ℕ) : ℝ :=
  ∑ p ∈ range z, if p ∈ P then primeDensity p else 0

theorem primeDensityMass_nonneg (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p) (z : ℕ) :
    0 ≤ primeDensityMass P z := by
  apply sum_nonneg
  intro p _
  split_ifs with hp
  · exact (primeDensity_bounds (hP p hp) (hodd p hp)).1
  · exact le_rfl

theorem sum_Ico_rosserStoppingMass_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (N M z : ℕ) (upper : Bool) (D : ℝ) :
    (∑ n ∈ Ico N M, rosserStoppingMass P n z upper D) ≤
      (primeDensityMass P z ^ N / N.factorial) * Real.exp (primeDensityMass P z) := by
  apply (sum_le_sum (fun n _ => rosserStoppingMass_le_factorial P hP hodd n z upper D)).trans
  exact sum_Ico_pow_div_factorial_le _ (primeDensityMass_nonneg P hP hodd z) N M

/-- The remainder after any finite number of depth terms is nonnegative
and has an explicit factorial tail bound. This controls the actual
Rosser defect, not an assumed continuous approximation. -/
theorem rosserDefect_partial_bounds (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (N z : ℕ) (upper : Bool) (D : ℝ) :
    0 ≤ rosserDefect P primeDensity z upper D -
      (∑ n ∈ range N, rosserStoppingMass P n z upper D) ∧
    rosserDefect P primeDensity z upper D -
      (∑ n ∈ range N, rosserStoppingMass P n z upper D) ≤
        (primeDensityMass P z ^ N / N.factorial) * Real.exp (primeDensityMass P z) := by
  by_cases hN : N ≤ z + 1
  · have hid := sum_range_add_sum_Ico (fun n => rosserStoppingMass P n z upper D) hN
    rw [← rosserDefect_eq_sum_stoppingMass P z upper D] at hid
    have heq : rosserDefect P primeDensity z upper D -
        (∑ n ∈ range N, rosserStoppingMass P n z upper D) =
          ∑ n ∈ Ico N (z + 1), rosserStoppingMass P n z upper D := by linarith
    rw [heq]
    exact ⟨sum_nonneg (fun n _ => rosserStoppingMass_nonneg P hP hodd n z upper D),
      sum_Ico_rosserStoppingMass_le P hP hodd N (z + 1) z upper D⟩
  · rw [sum_range_rosserStoppingMass_eq_defect P N z upper D (by omega), sub_self]
    have hL := primeDensityMass_nonneg P hP hodd z
    constructor
    · exact le_rfl
    · positivity

end Chen.LinearSieve
