import ChenTheorem.Lemma9.LinearSieve.GrowingPrefixCutoff

open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem tendsto_log_twice_growing_div_log (d : ℝ) :
    Tendsto (fun L => Real.log (2 * growingSieveParameter d L) / Real.log L)
      atTop (𝓝 (1 / d)) := by
  have hc : Tendsto (fun L : ℝ => Real.log 2 / Real.log L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h := hc.add (tendsto_log_growingSieveParameter_div_log d)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (growingSieveParameter_pos d L hL).ne', add_div]

/-- A cubic growing-range budget still vanishes after division by any
power larger than `3/d`. It controls density losses against the contraction gap. -/
theorem tendsto_growingDensityBudget_zero (d β : ℝ) (hβ : 3 / d < β) :
    Tendsto (fun L => (2 * growingSieveParameter d L) ^ 3 *
      Real.log (2 * growingSieveParameter d L) / L ^ β) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun L : ℝ => (Real.log L) ^ 4 / L ^ (β - 3 / d)) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using
      (isLittleO_log_rpow_rpow_atTop (4 : ℝ) (show 0 < β - 3 / d by linarith)).tendsto_div_nhds_zero
  have h := (hsmall.mul (tendsto_log_twice_growing_div_log d)).const_mul 8
  simp only [zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  have hL0 : 0 < L := by linarith
  have hlog := (Real.log_pos hL).ne'
  have hpow : (L ^ (1 / d)) ^ 3 = L ^ (3 / d) := by
    have hp := Real.rpow_mul hL0.le (1 / d) 3
    have he : (1 / d) * 3 = 3 / d := by ring
    rw [he, Real.rpow_ofNat] at hp
    exact hp.symm
  rw [Real.rpow_sub hL0]
  unfold growingSieveParameter
  rw [mul_pow, mul_pow, hpow]
  field_simp
  ring

end Chen.LinearSieve
