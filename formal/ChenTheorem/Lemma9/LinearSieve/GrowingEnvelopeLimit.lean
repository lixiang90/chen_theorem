import ChenTheorem.Lemma9.LinearSieve.GrowingSieveParameter

open Filter Set
open scoped Topology

namespace Chen.LinearSieve

theorem tendsto_log_log_mass_sub (C : ℝ) (hC : 0 < C) :
    Tendsto (fun L => Real.log (1 + Real.log (C * L)) - Real.log (Real.log L))
      atTop (𝓝 0) := by
  have hsmall : Tendsto (fun L => (1 + Real.log C) / Real.log L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hratio : Tendsto (fun L => (1 + Real.log (C * L)) / Real.log L) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hsmall
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
    rw [Real.log_mul hC.ne' (by linarith : L ≠ 0)]
    have hlog := (Real.log_pos hL).ne'
    field_simp
    ring
  have h := hratio.log (by norm_num : (1 : ℝ) ≠ 0)
  simp only [Real.log_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (max 1 (1 / C))] with L hL
  have hL1 : 1 < L := (le_max_left _ _).trans_lt hL
  have hCL : 1 < C * L := by
    have h := (div_lt_iff₀ hC).mp ((le_max_right _ _).trans_lt hL)
    nlinarith
  exact Real.log_div (by have := Real.log_pos hCL; linarith) (Real.log_pos hL1).ne'

theorem tendsto_comparisonEnvelope_prefactor (C d δ : ℝ) (hC : 0 < C) (hd : 0 < d) :
    Tendsto (fun L => (2 * Real.log (C * L) + |δ| * Real.log L +
      |Real.log auxiliaryLowerConstant|) / growingSieveParameter d L) atTop (𝓝 0) := by
  have hc : Tendsto (fun L => (2 * Real.log C + |Real.log auxiliaryLowerConstant|) /
      growingSieveParameter d L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_growingSieveParameter_atTop d hd)
  have h := hc.add ((tendsto_log_div_growingSieveParameter d hd).mul_const (2 + |δ|))
  simp only [zero_mul, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  rw [Real.log_mul hC.ne' (by linarith : L ≠ 0)]
  ring

/-- Subtracting the divergent main term leaves a finite limit. The
coefficient `d - 2` is positive in the large-parameter regime. -/
theorem tendsto_comparisonEnvelope_renormalized (C d δ : ℝ) (hC : 0 < C) (hd : 0 < d) :
    Tendsto (fun L => comparisonEnvelope (C * L) d δ L (growingSieveParameter d L) +
      (d - 2) * Real.log (Real.log L)) atTop (𝓝 (8 + Real.log (1 / d))) := by
  have h := ((((tendsto_comparisonEnvelope_prefactor C d δ hC hd).add
    ((tendsto_log_growingSieveParameter_div_self d hd).mul_const 2)).add_const 8).add
      (tendsto_log_log_mass_sub C hC)).add (tendsto_log_log_growingSieveParameter_sub d hd)
  simp only [zero_mul, zero_add, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  have he : d * Real.log (growingSieveParameter d L) =
      Real.log L + d * Real.log (Real.log L) := by
    rw [log_growingSieveParameter d L hL]
    field_simp
  dsimp only [comparisonEnvelope]
  nlinarith

theorem eventually_comparisonEnvelope_le_neg_one (C d δ : ℝ) (hC : 0 < C) (hd : 2 < d) :
    ∀ᶠ L in atTop, comparisonEnvelope (C * L) d δ L (growingSieveParameter d L) ≤ -1 := by
  have hlim := tendsto_comparisonEnvelope_renormalized C d δ hC (by linarith)
  have hupper := hlim.eventually (Iio_mem_nhds
    (by linarith : 8 + Real.log (1 / d) < (8 + Real.log (1 / d)) + 1))
  have hlower := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
    (((8 + Real.log (1 / d)) + 2) / (d - 2))
  filter_upwards [hupper, hlower] with L hu hl
  have h := (div_le_iff₀ (by linarith : 0 < d - 2)).mp hl
  dsimp only [Function.comp_def] at h
  change comparisonEnvelope (C * L) d δ L (growingSieveParameter d L) +
    (d - 2) * Real.log (Real.log L) < (8 + Real.log (1 / d)) + 1 at hu
  nlinarith

end Chen.LinearSieve
