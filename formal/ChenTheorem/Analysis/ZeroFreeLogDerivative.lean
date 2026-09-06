import ChenTheorem.Analysis.AnalyticLogBranch
import Mathlib.Analysis.Complex.BorelCaratheodory

open Set Metric

namespace Chen

/-- A normalized holomorphic logarithm with real part at most `M` has norm
at most `14 M` on the disk with seven eighths of the original radius. -/
theorem norm_analyticLog_le_on_inner_ball (g : ℂ → ℂ) (c : ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 < M) (hg : DifferentiableOn ℂ g (ball c R))
    (hc : g c = 0) (hbound : ∀ z ∈ ball c R, (g z).re ≤ M)
    (z : ℂ) (hz : dist z c < 7 * R / 8) : ‖g z‖ ≤ 14 * M := by
  let G : ℂ → ℂ := fun w => g (c + w)
  have hmem (w : ℂ) (hw : w ∈ ball (0 : ℂ) R) : c + w ∈ ball c R := by
    simpa only [mem_ball, dist_zero_right, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw
  have hG : DifferentiableOn ℂ G (ball 0 R) :=
    hg.comp (by fun_prop : DifferentiableOn ℂ (fun w => c + w) (ball 0 R)) hmem
  have hGc : G 0 = 0 := by simp [G, hc]
  have hzb : z - c ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, ← dist_eq_norm]
    linarith
  have hb := Complex.borelCaratheodory_zero hM hG (fun w hw => hbound _ (hmem w hw)) hR hzb hGc
  have hnorm : ‖z - c‖ < 7 * R / 8 := by simpa only [dist_eq_norm] using hz
  have hden : 0 < R - ‖z - c‖ := by linarith
  have hratio : 2 * M * ‖z - c‖ / (R - ‖z - c‖) ≤ 14 * M := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  simpa only [G, add_sub_cancel] using hb.trans hratio

/-- Growth relative to a nonzero center value controls the logarithmic
derivative on the three-quarter disk, provided that the whole disk is zero-free.
The constants are absolute and no arithmetic assumptions are used. -/
theorem norm_logDeriv_le_of_nonvanishing_ball (f : ℂ → ℂ) (c : ℂ) (R M : ℝ)
    (hR : 0 < R) (hM : 0 < M) (hf : DifferentiableOn ℂ f (ball c R))
    (hne : ∀ z ∈ ball c R, f z ≠ 0)
    (hbound : ∀ z ∈ ball c R, ‖f z‖ ≤ Real.exp M * ‖f c‖)
    (z : ℂ) (hz : dist z c ≤ 3 * R / 4) : ‖deriv f z / f z‖ ≤ 224 * M / R := by
  obtain ⟨g, hg, hgc, hge⟩ := exists_normalized_analyticLog_on_ball f c R hR hf hne
  have hc : f c ≠ 0 := hne c (mem_ball_self hR)
  have hreal : ∀ w ∈ ball c R, (g w).re ≤ M := by
    intro w hw
    apply Real.exp_le_exp.mp
    rw [← Complex.norm_exp, hge w hw, norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hc)).mpr (hbound w hw)
  have hinner : ∀ w, dist w c < 7 * R / 8 → ‖g w‖ ≤ 14 * M :=
    norm_analyticLog_le_on_inner_ball g c R M hR hM hg hgc hreal
  have hzinner : dist z c < 7 * R / 8 := by linarith
  have hsub : ball z (R / 8) ⊆ ball c R := by
    intro w hw
    have hdist := dist_triangle w z c
    change dist w z < R / 8 at hw
    change dist w c < R
    linarith
  have hmapping : MapsTo g (ball z (R / 8)) (closedBall (g z) (28 * M)) := by
    intro w hw
    have hwinner : dist w c < 7 * R / 8 := by
      have hdist := dist_triangle w z c
      change dist w z < R / 8 at hw
      linarith
    change dist (g w) (g z) ≤ 28 * M
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hinner w hwinner, hinner z hzinner])
  have hd := Complex.norm_deriv_le_div_of_mapsTo_ball (hg.mono hsub) hmapping (by positivity : 0 < R / 8)
  rw [deriv_analyticLog_eq_logDeriv isOpen_ball hf hg c hc hge z (by
    change dist z c < R
    linarith)] at hd
  convert hd using 1
  ring

end Chen
