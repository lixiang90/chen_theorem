import ChenTheorem.Analysis.LocalZeroLogDerivative
import ChenTheorem.Analysis.DiskZeroCount

open Set Metric

namespace Chen

/-- A fully quantitative local logarithmic-derivative expansion. Analyticity
and a bound on a slightly larger disk suffice; there is no nonvanishing
assumption on the disks, only at their center and at the evaluation point. -/
theorem norm_logDeriv_sub_zero_poles_le_of_outer_bound {f : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (4 * R / 3))) (h0 : f 0 ≠ 0)
    (hb : ∀ w ∈ sphere 0 (4 * R / 3), ‖f w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ 3 * R / 4) (hfz : f z ≠ 0) :
    ‖deriv f z / f z - diskZeroPoleSum f R z‖ ≤
      240 * (Real.log (M / ‖f 0‖) + 1) / R := by
  let B := Real.log (M / ‖f 0‖) + 1
  have houter : 0 < 4 * R / 3 := by positivity
  have hsub : R ≤ 4 * R / 3 := by linarith
  have hnorm0 : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
  have hcenter : ‖f 0‖ ≤ M := norm_le_of_analyticOnNhd_closedBall houter hf hb
    (mem_closedBall_self houter.le)
  have hratio : 1 ≤ M / ‖f 0‖ := (one_le_div hnorm0).mpr hcenter
  have hlog : 0 ≤ Real.log (M / ‖f 0‖) := Real.log_nonneg hratio
  have hB : 0 < B := by dsimp [B]; linarith
  have hgrowth : M ≤ Real.exp B * ‖f 0‖ := by
    calc
      M = Real.exp (Real.log (M / ‖f 0‖)) * ‖f 0‖ := by
        rw [Real.exp_log (by positivity)]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (by dsimp [B]; linarith)) hnorm0.le
  have hbinner : ∀ w ∈ sphere 0 R, ‖f w‖ ≤ Real.exp B * ‖f 0‖ := by
    intro w hw
    exact (norm_le_of_analyticOnNhd_closedBall houter hf hb
      (closedBall_subset_closedBall hsub (sphere_subset_closedBall hw))).trans hgrowth
  have hcount := diskZeroCount_le_of_outer_bound hR (by linarith : R < 4 * R / 3) hM hf h0 hb
  rw [show (4 * R / 3) / R = (4 / 3 : ℝ) by field_simp] at hcount
  have hden : (1 / 4 : ℝ) ≤ Real.log (4 / 3 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    norm_num at h
    exact h
  have hcountB : diskZeroCount f R ≤ 4 * B := by
    apply hcount.trans
    apply (div_le_iff₀ (by linarith : 0 < Real.log (4 / 3 : ℝ))).mpr
    dsimp [B]
    nlinarith
  have hlocal := norm_logDeriv_sub_diskZeroPoleSum_le hR hB
    (hf.mono (closedBall_subset_closedBall hsub)) h0 hbinner hz hfz
  apply hlocal.trans
  apply div_le_div_of_nonneg_right _ hR.le
  change 224 * B + 4 * diskZeroCount f R ≤ 240 * B
  linarith

end Chen
