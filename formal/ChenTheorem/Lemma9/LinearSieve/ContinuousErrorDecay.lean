import ChenTheorem.Lemma9.LinearSieve.ContinuousErrorDerivative
import Mathlib.Analysis.Normed.Group.Tannery

open Set Filter
open scoped Topology

namespace Chen.LinearSieve

theorem tendsto_mul_rosserContinuousTerm_zero (n : ℕ) :
    Tendsto (fun s : ℝ => s * rosserContinuousTerm n s) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ((n : ℝ) + 2)] with s hs
  rw [rosserContinuousTerm_eq_zero n s hs, mul_zero]

theorem norm_mul_rosserContinuousTerm_le (n : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    ‖s * rosserContinuousTerm n s‖ ≤ 2 * rosserContinuousTerm n 2 := by
  have hs0 : 0 < s := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hs0.le (rosserContinuousTerm_nonneg n s hs0))]
  exact antitoneOn_mul_rosserContinuousTerm n (by norm_num) hs0 hs

/-- The weighted errors tend to zero, not merely to an unspecified
nonnegative limit. Compact support of each summand and a summable
uniform bound justify the limit through the series. -/
theorem tendsto_mul_upperContinuousError_zero :
    Tendsto (fun s : ℝ => s * upperContinuousError s) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    ((summable_odd_rosserContinuousTerm 2 (by norm_num)).mul_left 2)
    (fun N => tendsto_mul_rosserContinuousTerm_zero (2 * N + 1)) (by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
      intro N
      exact norm_mul_rosserContinuousTerm_le _ s hs)
  simpa only [tsum_mul_left, tsum_zero, upperContinuousError] using h

theorem tendsto_mul_lowerContinuousError_zero :
    Tendsto (fun s : ℝ => s * lowerContinuousError s) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    ((summable_even_rosserContinuousTerm 2 le_rfl).mul_left 2)
    (fun N => tendsto_mul_rosserContinuousTerm_zero (2 * N + 2)) (by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
      intro N
      exact norm_mul_rosserContinuousTerm_le _ s hs)
  simpa only [tsum_mul_left, tsum_zero, lowerContinuousError] using h

theorem tendsto_upperContinuousError_zero : Tendsto upperContinuousError atTop (𝓝 0) := by
  have h := tendsto_mul_upperContinuousError_zero.mul tendsto_inv_atTop_zero
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  field_simp

theorem tendsto_lowerContinuousError_zero : Tendsto lowerContinuousError atTop (𝓝 0) := by
  have h := tendsto_mul_lowerContinuousError_zero.mul tendsto_inv_atTop_zero
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  field_simp

end Chen.LinearSieve
