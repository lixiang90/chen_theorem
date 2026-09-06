import ChenTheorem.Lemma9.LinearSieve.InflationContractionGap

open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem auxiliaryInflationSlope_zero_le_power (d D t : ℝ) (hd : 0 ≤ d) (hD : 1 < D) (ht : 0 < t) :
    auxiliaryInflationSlope d D 0 t ≤ (d + 1) * (t ^ d / Real.log D) := by
  have hp := Real.rpow_nonneg ht.le d
  have hL := Real.log_pos hD
  have hb : 0 < 1 + t ^ d / Real.log D := by positivity
  have hl := Real.log_le_sub_one_of_pos hb
  have hs := auxiliaryInflationSlope_le d D 0 t hd hD le_rfl ht
  simp only [add_zero] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))

/-- The inflation slope consumes at most half of the combined child loss,
uniformly over the growing interval. -/
theorem eventually_auxiliaryInflationSlope_gap (d α k : ℝ) (hd : 0 < d)
    (hα : 0 < α) (hα1 : α ≤ 1) (hk : 0 < k) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ t : ℝ, 2 ≤ t →
      t ≤ 2 * growingSieveParameter d (Real.log D) →
      auxiliaryInflationSlope d D 0 t ≤ k * Real.log t *
        inflationContractionGap α (t ^ d / Real.log D) t / 2 := by
  have hlogT := (Real.tendsto_log_atTop.const_mul_atTop hk).eventually_ge_atTop (4 * (d + 1))
  obtain ⟨T, hT2, hTk⟩ := ((eventually_ge_atTop (2 : ℝ)).and hlogT).exists
  have hT : 0 < T := by linarith
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlim : Tendsto (fun D : ℝ => (d + 1) * T ^ d / Real.log D) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hsmall := hlim.eventually (gt_mem_nhds (show 0 < k * Real.log 2 * α / (2 * T) by positivity))
  filter_upwards [eventually_auxiliaryInflationSlope_small_from_two d (k / 4) hd (by positivity), hsmall]
    with D hD hcompact
  refine ⟨hD.1, ?_⟩
  intro t ht hcut
  let x := t ^ d / Real.log D
  have ht0 : 0 < t := by linarith
  have hx : 0 ≤ x := div_nonneg (Real.rpow_nonneg ht0.le d) (Real.log_pos hD.1).le
  have hden : 0 < 1 + x := by linarith
  have hat : 0 ≤ α / t := div_nonneg hα.le ht0.le
  have hg := inflationContractionGap_bounds α x t hα.le hα1 hx (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht
  have hkl : 0 ≤ k * Real.log t := mul_nonneg hk.le (hl2.le.trans hlog)
  by_cases htT : t ≤ T
  · have hp := Real.rpow_le_rpow ht0.le htT hd.le
    have hpow := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hp (Real.log_pos hD.1).le) (show 0 ≤ d + 1 by linarith)
    have hsl := auxiliaryInflationSlope_zero_le_power d D t hd.le hD.1 ht0
    have hb : auxiliaryInflationSlope d D 0 t ≤ k * Real.log 2 * α / (2 * T) := by
      have he : (d + 1) * (T ^ d / Real.log D) = (d + 1) * T ^ d / Real.log D := by ring
      rw [he] at hpow
      exact (hsl.trans hpow).trans hcompact.le
    have haT := div_le_div_of_nonneg_left hα.le ht0 htT
    have hgap : α / T ≤ inflationContractionGap α x t := haT.trans hg.2.1
    have hm := mul_le_mul (mul_le_mul_of_nonneg_left hlog hk.le) hgap
      (div_nonneg hα.le hT.le) hkl
    have he : k * Real.log 2 * α / (2 * T) = (k * Real.log 2 * (α / T)) / 2 := by ring
    rw [he] at hb
    exact hb.trans (div_le_div_of_nonneg_right hm (by norm_num))
  · have hlarge : 4 * (d + 1) ≤ k * Real.log t :=
      hTk.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hT (le_of_not_ge htT)) hk.le)
    by_cases hx1 : x ≤ 1
    · have hgx : x / 2 ≤ inflationContractionGap α x t := by
        rw [inflationContractionGap, le_div_iff₀ hden]
        nlinarith
      have hs := auxiliaryInflationSlope_zero_le_power d D t hd.le hD.1 ht0
      change auxiliaryInflationSlope d D 0 t ≤ (d + 1) * x at hs
      have hmul := mul_le_mul_of_nonneg_right hlarge hx
      have hgap := mul_le_mul_of_nonneg_left hgx hkl
      nlinarith
    · have hgx : (1 / 2 : ℝ) ≤ inflationContractionGap α x t := by
        rw [inflationContractionGap, le_div_iff₀ hden]
        linarith [le_of_not_ge hx1]
      have hs := hD.2 0 le_rfl (by norm_num) t ht hcut
      have hgap := mul_le_mul_of_nonneg_left hgx hkl
      nlinarith

end Chen.LinearSieve
