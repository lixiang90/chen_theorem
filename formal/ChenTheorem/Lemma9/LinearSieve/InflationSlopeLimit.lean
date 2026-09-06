import ChenTheorem.Lemma9.LinearSieve.InflationLogBounds

open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem tendsto_inflationLogBudget_zero (d : ℝ) :
    Tendsto (inflationLogBudget d) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun L : ℝ => (2 : ℝ) ^ d / (L ^ (1 / 2 : ℝ) * Real.log 3))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).atTop_mul_const
      (Real.log_pos (by norm_num : (1 : ℝ) < 3)))
  have hconst : Tendsto (fun L : ℝ => Real.log (1 + (3 : ℝ) ^ d) / Real.log L)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hloglog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have hbig := (hconst.add (hloglog.const_mul d)).const_mul (2 * d)
  have h := hsmall.add hbig
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [] with L
  dsimp [inflationLogBudget, Function.comp_def]
  ring

/-- The inflation slope is negligible relative to `log s`, uniformly up to
twice the growing parameter and for every shift in `[0,1]`. -/
theorem eventually_auxiliaryInflationSlope_small (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      ∀ s : ℝ, 3 ≤ s → s ≤ 2 * growingSieveParameter d (Real.log D) →
        auxiliaryInflationSlope d D a s ≤ ε * Real.log s := by
  have hbudget := ((tendsto_inflationLogBudget_zero d).const_mul (d + 1)).comp Real.tendsto_log_atTop
  simp only [mul_zero] at hbudget
  have hL := Real.tendsto_log_atTop.eventually_gt_atTop 1
  have hlog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
  have hσ := ((tendsto_growingSieveParameter_atTop d hd).comp Real.tendsto_log_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_gt_atTop (1 : ℝ), hL, hlog, hσ,
    hbudget.eventually (gt_mem_nhds hε)] with D hD hL hlog hσ hb
  dsimp only [Function.comp_def] at hlog hσ hb
  refine ⟨hD, ?_⟩
  intro a ha ha1 s hs hcut
  have h := inflation_log_uniform_bound d (Real.log D) a s hd hL hlog hσ ha ha1 hs hcut
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ d + 1 by linarith)
  have hsl := auxiliaryInflationSlope_le d D a s hd.le hD ha (by linarith)
  have hls := (Real.log_pos (show 1 < s by linarith)).le
  have he := mul_le_mul_of_nonneg_right (le_of_lt hb) hls
  nlinarith

end Chen.LinearSieve
