import Submission.ChenTheorem.Lemma6.ZetaRightStripGrowth
import Submission.ChenTheorem.Lemma6.LFunctionZeroPoleRealPart

set_option autoImplicit true
open Set Metric

namespace Chen

theorem high_centered_zeta_ne_pole (t : ℝ) (ht : 1 ≤ |t|) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    dirichletZeroDiskCenter t + w ≠ 1 := by
  intro he
  have him := congrArg Complex.im he
  simp [dirichletZeroDiskCenter] at him
  have hwim := (Complex.abs_im_le_norm w).trans hw
  have ht' : |t| = |w.im| := by rw [show t = -w.im by linarith, abs_neg]
  rw [← ht'] at hwim
  linarith

theorem analyticOnNhd_high_centered_zeta (t : ℝ) (ht : 1 ≤ |t|) :
    AnalyticOnNhd ℂ (fun w => riemannZeta (dirichletZeroDiskCenter t + w))
      (closedBall 0 (1 / 2)) := by
  intro w hw
  have hne := high_centered_zeta_ne_pole t ht (by simpa only [mem_closedBall_zero_iff] using hw)
  exact (analyticOn_riemannZeta _ hne).comp (by fun_prop)

theorem norm_riemannZeta_zero_disk_center_ge (t : ℝ) :
    (1 / 5 : ℝ) ≤ ‖riemannZeta (dirichletZeroDiskCenter t)‖ := by
  simpa only [DirichletCharacter.LFunction_modOne_eq]
    using norm_LFunction_zero_disk_center_ge (1 : DirichletCharacter ℂ 1) t

theorem norm_riemannZeta_logDeriv_sub_local_zero_poles_le (t : ℝ) (ht : 1 ≤ |t|)
    (s : ℂ) (hs : ‖s - dirichletZeroDiskCenter t‖ ≤ 9 / 32) (hne : riemannZeta s ≠ 0) :
    ‖logDeriv riemannZeta s - diskZeroPoleSum
      (fun w => riemannZeta (dirichletZeroDiskCenter t + w)) (3 / 8)
      (s - dirichletZeroDiskCenter t)‖ ≤
      640 * (Real.log (20 * (‖dirichletZeroDiskCenter t‖ + 1)) + 1) := by
  let c := dirichletZeroDiskCenter t
  let F := fun w => riemannZeta (c + w)
  let M := 4 * (‖c‖ + 1)
  have hM : 1 ≤ M := by dsimp [M]; have := norm_nonneg c; linarith
  have hf : AnalyticOnNhd ℂ F (closedBall 0 (4 * (3 / 8) / 3)) := by
    convert analyticOnNhd_high_centered_zeta t ht using 1
    norm_num
  have hanchor : (1 / 5 : ℝ) ≤ ‖F 0‖ := by
    simpa only [F, add_zero] using norm_riemannZeta_zero_disk_center_ge t
  have hnorm0 : 0 < ‖F 0‖ := by linarith
  have hb : ∀ w ∈ sphere (0 : ℂ) (4 * (3 / 8) / 3), ‖F w‖ ≤ M := by
    intro w hw
    have hw' : ‖w‖ ≤ 1 / 2 := by norm_num [mem_sphere] at hw; exact hw.le
    exact norm_riemannZeta_high_centered_disk_le t ht hw'
  have he : c + (s - c) = s := by ring
  have hmain := norm_logDeriv_sub_zero_poles_le_of_outer_bound (by norm_num : (0 : ℝ) < 3 / 8)
    hM hf (norm_pos_iff.mp hnorm0) hb
    (show ‖s - c‖ ≤ 3 * (3 / 8) / 4 by norm_num; exact hs)
    (show F (s - c) ≠ 0 by simpa only [F, he] using hne)
  have hd : deriv F (s - c) = deriv riemannZeta s := by dsimp [F]; rw [deriv_comp_const_add, he]
  rw [hd, show F (s - c) = riemannZeta s by dsimp [F]; rw [he]] at hmain
  have hratio : M / ‖F 0‖ ≤ 5 * M := (div_le_iff₀ hnorm0).mpr (by nlinarith)
  have hlogs := Real.log_le_log (div_pos (by linarith : 0 < M) hnorm0) hratio
  change ‖deriv riemannZeta s / riemannZeta s - diskZeroPoleSum F (3 / 8) (s - c)‖ ≤ _
  have heM : 5 * M = 20 * (‖c‖ + 1) := by dsimp [M]; ring
  rw [heM] at hlogs
  apply hmain.trans
  change 240 * (Real.log (M / ‖F 0‖) + 1) / (3 / 8) ≤ 640 * (Real.log (20 * (‖c‖ + 1)) + 1)
  linarith

end Chen
