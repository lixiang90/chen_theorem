import Submission.ChenTheorem.Lemma6.ZetaLocalZeroLogDerivative

set_option autoImplicit true
namespace Chen

theorem height_log_ge_half (t : ℝ) : (1 / 2 : ℝ) ≤ Real.log (|t| + 2) := by
  have hA : 0 < |t| + 2 := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hA
  have hi : (|t| + 2)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (show 2 ≤ |t| + 2 by linarith [abs_nonneg t])
  linarith

theorem zeta_zero_disk_log_bound_le (t : ℝ) :
    Real.log (20 * (‖dirichletZeroDiskCenter t‖ + 1)) + 1 ≤ 93 * Real.log (|t| + 2) := by
  have hc : ‖dirichletZeroDiskCenter t‖ ≤ |t| + 5 / 4 := by
    have h := norm_add_le (5 / 4 : ℂ) ((t : ℂ) * Complex.I)
    norm_num [dirichletZeroDiskCenter, norm_mul] at h ⊢
    linarith
  have hA : 0 < |t| + 2 := by positivity
  have harg : 20 * (‖dirichletZeroDiskCenter t‖ + 1) ≤ 45 * (|t| + 2) := by
    nlinarith [abs_nonneg t]
  have hl := Real.log_le_log (by positivity : 0 < 20 * (‖dirichletZeroDiskCenter t‖ + 1)) harg
  rw [Real.log_mul (by norm_num : (45 : ℝ) ≠ 0) hA.ne'] at hl
  have h45 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 45)
  have hL := height_log_ge_half t
  linarith

theorem norm_riemannZeta_logDeriv_sub_local_zero_poles_le_log (t : ℝ) (ht : 1 ≤ |t|)
    (s : ℂ) (hs : ‖s - dirichletZeroDiskCenter t‖ ≤ 9 / 32) (hne : riemannZeta s ≠ 0) :
    ‖logDeriv riemannZeta s - diskZeroPoleSum
      (fun w => riemannZeta (dirichletZeroDiskCenter t + w)) (3 / 8)
      (s - dirichletZeroDiskCenter t)‖ ≤ 60000 * Real.log (|t| + 2) := by
  apply (norm_riemannZeta_logDeriv_sub_local_zero_poles_le t ht s hs hne).trans
  have h := zeta_zero_disk_log_bound_le t
  have hp := height_log_ge_half t
  linarith

theorem riemannZeta_logDeriv_re_ge_high (σ t : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2)
    (ht : 1 ≤ |t|) :
    -(60000 * Real.log (|t| + 2)) ≤
      (logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  have hne : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ)
  have hb := norm_riemannZeta_logDeriv_sub_local_zero_poles_le_log t ht _
    (norm_line_point_sub_dirichletZeroDiskCenter_le hσ hσ' t) hne
  have hf : AnalyticOnNhd ℂ (fun w => riemannZeta (dirichletZeroDiskCenter t + w))
      (Metric.closedBall 0 (3 / 8)) :=
    (analyticOnNhd_high_centered_zeta t ht).mono (Metric.closedBall_subset_closedBall (by norm_num))
  have hp := diskZeroPoleSum_re_nonneg (κ := -(1 / 4 : ℝ)) hf
    (fun w _ hw => by
      have h := centered_LFunction_ne_zero_of_re_gt_neg_quarter
        (1 : DirichletCharacter ℂ 1) t w hw
      simpa only [DirichletCharacter.LFunction_modOne_eq] using h)
    (z := (σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t)
    (by rw [line_point_sub_dirichletZeroDiskCenter, Complex.ofReal_re]; linarith)
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  rw [Complex.sub_re] at hr
  linarith

end Chen
