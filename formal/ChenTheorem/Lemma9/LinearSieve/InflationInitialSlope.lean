import ChenTheorem.Lemma9.LinearSieve.InflationSlopeLimit

open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem auxiliaryInflationSlope_initial_bound (d D a s : ℝ)
    (hd : 0 < d) (hD : 1 < D) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : 0 < s) (hs3 : s ≤ 3) :
    auxiliaryInflationSlope d D a s ≤ (d + 1) * (4 : ℝ) ^ d / Real.log D := by
  have hL := Real.log_pos hD
  have hpow := Real.rpow_le_rpow (show 0 ≤ s + a by linarith)
    (show s + a ≤ 4 by linarith) hd.le
  have hfrac := div_le_div_of_nonneg_right hpow hL.le
  have hbase : 0 < 1 + (s + a) ^ d / Real.log D := by
    have := Real.rpow_nonneg (show 0 ≤ s + a by linarith) d
    positivity
  have hlog := Real.log_le_sub_one_of_pos hbase
  have hlog' : Real.log (1 + (s + a) ^ d / Real.log D) ≤ (4 : ℝ) ^ d / Real.log D := by linarith
  have h := (auxiliaryInflationSlope_le d D a s hd.le hD ha hs).trans
    (mul_le_mul_of_nonneg_left hlog' (by linarith))
  simpa only [mul_div_assoc] using h

/-- The slope bound extends to two using a direct estimate on the initial
compact interval; no differentiability at the junction is assumed. -/
theorem eventually_auxiliaryInflationSlope_small_from_two (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      ∀ s : ℝ, 2 ≤ s → s ≤ 2 * growingSieveParameter d (Real.log D) →
        auxiliaryInflationSlope d D a s ≤ ε * Real.log s := by
  have hlim : Tendsto (fun D : ℝ => (d + 1) * (4 : ℝ) ^ d / Real.log D) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  filter_upwards [eventually_auxiliaryInflationSlope_small d ε hd hε,
    hlim.eventually (gt_mem_nhds (mul_pos hε hlog2))] with D hD hsmall
  refine ⟨hD.1, ?_⟩
  intro a ha ha1 s hs hcut
  by_cases hs3 : 3 ≤ s
  · exact hD.2 a ha ha1 s hs3 hcut
  · have h := auxiliaryInflationSlope_initial_bound d D a s hd hD.1 ha ha1 (by linarith) (le_of_not_ge hs3)
    have hl := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num : (0 : ℝ) < 2) hs) hε.le
    exact h.trans (hsmall.le.trans hl)

end Chen.LinearSieve
