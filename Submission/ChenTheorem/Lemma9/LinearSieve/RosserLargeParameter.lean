import Submission.ChenTheorem.Lemma9.LinearSieve.RosserMassLogBound

set_option autoImplicit true
open Finset

namespace Chen.LinearSieve

/-- At a sufficiently high level, all shallow stopping contributions
vanish exactly. Only the factorially controlled depth tail remains. -/
theorem sum_range_rosserStoppingMass_eq_zero_of_level (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N z : ℕ) (hz : 1 ≤ z) (upper : Bool) (D : ℝ)
    (hD : (z : ℝ) ^ (N + 1) < D) :
    (∑ n ∈ range N, rosserStoppingMass P n z upper D) = 0 := by
  apply sum_eq_zero
  intro n hn
  apply rosserStoppingMass_eq_zero_of_level P hP n z upper D
  have hzR : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hpow := pow_le_pow_right₀ hzR (show n + 2 ≤ N + 1 by have := mem_range.mp hn; omega)
  exact hpow.trans_lt hD

theorem rosserDefect_le_factorial_of_level (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (N z : ℕ) (hz : 1 ≤ z) (upper : Bool) (D : ℝ)
    (hD : (z : ℝ) ^ (N + 1) < D) :
    rosserDefect P primeDensity z upper D ≤
      (primeDensityMass P z ^ N / N.factorial) * Real.exp (primeDensityMass P z) := by
  have h := (rosserDefect_partial_bounds P hP hodd N z upper D).2
  rwa [sum_range_rosserStoppingMass_eq_zero_of_level P hP N z hz upper D hD, sub_zero] at h

/-- Uniform large-parameter control for the normalized Rosser defect.
The bound uses only the fixed dimension-one constant, `z`, and the
chosen depth `N`; no later-state comparison is assumed. -/
theorem rosserRelativeDefect_large_parameter_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℕ, 2 ≤ z → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) → ∀ N : ℕ, ∀ upper : Bool, ∀ D : ℝ,
      ((z + 1 : ℕ) : ℝ) ^ (N + 1) < D →
      rosserRelativeDefect P (z + 1) upper D ≤
        ((1 + K / Real.log 2) * (Real.log z / Real.log 2)) ^ 2 *
        (Real.log ((1 + K / Real.log 2) * (Real.log z / Real.log 2)) ^ N / N.factorial) := by
  obtain ⟨K, hK, hb⟩ := primeDensityMass_dimension_one
  refine ⟨K, hK, ?_⟩
  intro z hz P hP hodd N upper D hD
  obtain ⟨hlog, hexp, hinv⟩ := hb z hz P hP hodd
  have hL := primeDensityMass_nonneg P hP hodd (z + 1)
  have hlog0 := hL.trans hlog
  have hV := primeDensity_sieveProduct_pos P hP hodd (z + 1)
  have hB : 0 ≤ (1 + K / Real.log 2) * (Real.log z / Real.log 2) :=
    (Real.exp_pos _).le.trans hexp
  have hdef := rosserDefect_le_factorial_of_level P hP hodd N (z + 1) (by omega) upper D hD
  unfold rosserRelativeDefect
  rw [div_eq_mul_inv]
  calc
    _ ≤ ((primeDensityMass P (z + 1) ^ N / N.factorial) * Real.exp (primeDensityMass P (z + 1))) *
        (sieveProduct P primeDensity (z + 1))⁻¹ :=
      mul_le_mul_of_nonneg_right hdef (inv_nonneg.mpr hV.le)
    _ ≤ (Real.log ((1 + K / Real.log 2) * (Real.log z / Real.log 2)) ^ N / N.factorial) *
        ((1 + K / Real.log 2) * (Real.log z / Real.log 2)) *
        ((1 + K / Real.log 2) * (Real.log z / Real.log 2)) := by gcongr
    _ = _ := by ring

end Chen.LinearSieve
