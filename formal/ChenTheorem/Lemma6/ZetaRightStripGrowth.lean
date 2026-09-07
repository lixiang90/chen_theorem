import ChenTheorem.Analysis.PNT.ZetaBounds
import ChenTheorem.Lemma6.LFunctionLocalZeroLogDerivative

open Set Metric

namespace Chen

theorem riemannZeta_eq_half_add_pole_add_integral (s : ℂ) (hs : 0 < s.re) (hsne : s ≠ 1) :
    riemannZeta s = (1 / 2 : ℂ) + 1 / (s - 1) +
      s * ∫ x in Ioi (1 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) := by
  have hs0 : s ≠ 0 := by intro he; rw [he] at hs; norm_num at hs
  rw [← Zeta0EqZeta (N := 1) (by norm_num) hs hsne]
  norm_num [riemannZeta0, Finset.sum_range_succ, Complex.zero_cpow, hs0]
  rw [show (1 : ℂ) - s = -(s - 1) by ring, div_neg]
  ring

theorem norm_riemannZeta_le_right_strip (s : ℂ) (hs : 0 < s.re) (hsne : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖s - 1‖ + ‖s‖ / s.re := by
  have hI := ZetaBnd_aux1b 1 (by norm_num) (σ := s.re) (t := s.im) hs
  rw [Complex.re_add_im] at hI
  norm_num only [Nat.cast_one, Real.one_rpow] at hI
  rw [riemannZeta_eq_half_add_pole_add_integral s hs hsne]
  apply (norm_add_le _ _).trans
  have hleft : ‖(1 / 2 : ℂ) + 1 / (s - 1)‖ ≤ 1 / 2 + 1 / ‖s - 1‖ := by
    simpa using norm_add_le (1 / 2 : ℂ) (1 / (s - 1))
  have hright : ‖s * ∫ x in Ioi (1 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      ‖s‖ / s.re := by
    rw [norm_mul]
    simpa only [one_div, div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hI (norm_nonneg s)
  linarith

theorem norm_riemannZeta_high_centered_disk_le (t : ℝ) (ht : 1 ≤ |t|)
    {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖riemannZeta (dirichletZeroDiskCenter t + w)‖ ≤
      4 * (‖dirichletZeroDiskCenter t‖ + 1) := by
  let c := dirichletZeroDiskCenter t
  let s := c + w
  have hre : 3 / 4 ≤ s.re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm w).trans hw)).1
    dsimp [s, c]
    rw [dirichletZeroDiskCenter_re]
    linarith
  have hc : 1 ≤ ‖c - 1‖ := by
    have h := Complex.abs_im_le_norm (c - 1)
    have h' : |t| ≤ ‖c - 1‖ := by simpa [c, dirichletZeroDiskCenter] using h
    exact ht.trans h'
  have hden : 1 / 2 ≤ ‖s - 1‖ := by
    have h := norm_sub_le (s - 1) w
    have he : s - 1 - w = c - 1 := by dsimp [s]; ring
    rw [he] at h
    linarith
  have hsne : s ≠ 1 := by intro he; rw [he, sub_self, norm_zero] at hden; norm_num at hden
  have hb := norm_riemannZeta_le_right_strip s (by linarith) hsne
  have hnorm : ‖s‖ ≤ ‖c‖ + 1 / 2 := (norm_add_le _ _).trans (by linarith)
  have hinv : 1 / ‖s - 1‖ ≤ 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden
    norm_num at h
    simpa only [one_div] using h
  have hquot : ‖s‖ / s.re ≤ 2 * ‖s‖ := by
    apply (div_le_iff₀ (by linarith : 0 < s.re)).mpr
    nlinarith [norm_nonneg s]
  change ‖riemannZeta s‖ ≤ 4 * (‖c‖ + 1)
  linarith [norm_nonneg c]

end Chen
