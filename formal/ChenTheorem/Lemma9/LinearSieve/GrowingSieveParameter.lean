import ChenTheorem.Lemma9.LinearSieve.ComparisonEnvelope

open Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The logarithmic level is `L = log D`; this is the growing parameter
at which the large-parameter comparison will be checked. -/
noncomputable def growingSieveParameter (d L : ℝ) : ℝ := L ^ (1 / d) * Real.log L

theorem growingSieveParameter_pos (d L : ℝ) (hL : 1 < L) :
    0 < growingSieveParameter d L :=
  mul_pos (Real.rpow_pos_of_pos (by linarith : 0 < L) _) (Real.log_pos hL)

theorem tendsto_growingSieveParameter_atTop (d : ℝ) (hd : 0 < d) :
    Tendsto (growingSieveParameter d) atTop atTop :=
  (tendsto_rpow_atTop (one_div_pos.mpr hd)).atTop_mul_atTop₀ Real.tendsto_log_atTop

theorem log_growingSieveParameter (d L : ℝ) (hL : 1 < L) :
    Real.log (growingSieveParameter d L) = (1 / d) * Real.log L + Real.log (Real.log L) := by
  rw [growingSieveParameter, Real.log_mul
    (Real.rpow_pos_of_pos (by linarith : 0 < L) _).ne' (Real.log_pos hL).ne',
    Real.log_rpow (by linarith : 0 < L)]

theorem tendsto_log_growingSieveParameter_div_log (d : ℝ) :
    Tendsto (fun L => Real.log (growingSieveParameter d L) / Real.log L)
      atTop (𝓝 (1 / d)) := by
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have h := (tendsto_const_nhds (x := 1 / d)).add hsmall
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  rw [log_growingSieveParameter d L hL]
  dsimp only [id_eq, Function.comp_def]
  simp [add_div, (Real.log_pos hL).ne']

theorem tendsto_log_log_growingSieveParameter_sub (d : ℝ) (hd : 0 < d) :
    Tendsto (fun L => Real.log (Real.log (growingSieveParameter d L)) - Real.log (Real.log L))
      atTop (𝓝 (Real.log (1 / d))) := by
  have h := (tendsto_log_growingSieveParameter_div_log d).log (one_div_pos.mpr hd).ne'
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_growingSieveParameter_atTop d hd).eventually_gt_atTop 1] with L hL hs
  exact Real.log_div (Real.log_pos hs).ne' (Real.log_pos hL).ne'

theorem tendsto_log_div_growingSieveParameter (d : ℝ) (hd : 0 < d) :
    Tendsto (fun L => Real.log L / growingSieveParameter d L) atTop (𝓝 0) := by
  have h : Tendsto (fun L : ℝ => 1 / L ^ (1 / d)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (one_div_pos.mpr hd))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  unfold growingSieveParameter
  have hlog := (Real.log_pos hL).ne'
  field_simp

theorem tendsto_log_growingSieveParameter_div_self (d : ℝ) (hd : 0 < d) :
    Tendsto (fun L => Real.log (growingSieveParameter d L) / growingSieveParameter d L)
      atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (tendsto_growingSieveParameter_atTop d hd)

end Chen.LinearSieve
