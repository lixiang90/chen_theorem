import ChenTheorem.Lemma6.ZetaRightStripGrowth

namespace Chen

theorem siegel_circle_geometry {s : ℂ} (hs : s ∈ Metric.sphere (2 : ℂ) (3 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ s.re ∧ ‖s‖ ≤ 7 / 2 ∧ (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
  have hnorm : ‖s - 2‖ = (3 / 2 : ℝ) := by simpa only [Metric.mem_sphere, dist_eq_norm] using hs
  have hre := (Complex.abs_re_le_norm (s - 2))
  have hnorms := norm_add_le (s - 2) (2 : ℂ)
  have hpole := norm_sub_le (s - 1) (1 : ℂ)
  norm_num only [Complex.sub_re, Complex.re_ofNat, hnorm, Complex.norm_ofNat,
    norm_one, sub_add_cancel] at hre hnorms hpole
  rw [show s - 1 - 1 = s - 2 by ring, hnorm] at hpole
  norm_num at hpole
  exact ⟨by linarith [(abs_le.mp hre).1], by linarith, by linarith⟩

theorem norm_riemannZeta_siegel_circle_le {s : ℂ}
    (hs : s ∈ Metric.sphere (2 : ℂ) (3 / 2 : ℝ)) : ‖riemannZeta s‖ ≤ 10 := by
  obtain ⟨hre, hnorm, hpole⟩ := siegel_circle_geometry hs
  have hsne : s ≠ 1 := by intro h; norm_num [h] at hpole
  have hb := norm_riemannZeta_le_right_strip (s := s) (by linarith) hsne
  have h1 : 1 / ‖s - 1‖ ≤ (2 : ℝ) := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have h2 : ‖s‖ / s.re ≤ (7 : ℝ) := (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

end Chen
