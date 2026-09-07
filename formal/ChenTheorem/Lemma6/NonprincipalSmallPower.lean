import ChenTheorem.Analysis.TwoDiskInterpolation
import ChenTheorem.Analysis.SmallPowerDiskGeometry
import ChenTheorem.Lemma6.NonprincipalCompactGrowth
import ChenTheorem.Lemma6.LFunctionEulerBounds

namespace Chen

/-- The L-function of every nonprincipal character has an arbitrarily small
conductor-power bound on a common neighborhood of one. -/
theorem exists_nonprincipal_small_power_disk {ε : ℝ} (hε : 0 < ε) :
    ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 2 ≤ q → χ ≠ 1 →
        ∀ s : ℂ, ‖s - 1‖ ≤ r → ‖DirichletCharacter.LFunction χ s‖ ≤ K * (q : ℝ) ^ ε := by
  obtain ⟨r, hr, hrsmall, hrR, hscale⟩ := exists_small_power_disk_radius hε
  let c : ℂ := ((1 + 2 * r : ℝ) : ℂ)
  have hcN : ‖c‖ = 1 + 2 * r := Complex.norm_of_nonneg (by linarith)
  have hAc : 1 ≤ 1 + 1 / r := by linarith [one_div_pos.mpr hr]
  refine ⟨r, (1 + 1 / r) * 42, hr, by positivity, ?_⟩
  intro q inst χ hq hχ s hs
  have hinner (w : ℂ) (hw : ‖w - c‖ ≤ r) : ‖DirichletCharacter.LFunction χ w‖ ≤ 1 + 1 / r := by
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (w - c)).trans hw)).1
    simp only [Complex.sub_re, c, Complex.ofReal_re] at hre
    have hwre : 1 < w.re := by linarith
    have hb := norm_LFunction_euler_upper χ w hwre
    have hi : 1 / (w.re - 1) ≤ 1 / r := one_div_le_one_div_of_le hr (by linarith)
    linarith
  have houter (w : ℂ) (hw : ‖w - c‖ ≤ (1 / 4 : ℝ)) :
      ‖DirichletCharacter.LFunction χ w‖ ≤ 42 * (q : ℝ) ^ 3 := by
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (w - c)).trans hw)).1
    simp only [Complex.sub_re, c, Complex.ofReal_re] at hre
    have hN := norm_add_le (w - c) c
    rw [sub_add_cancel, hcN] at hN
    apply norm_nonprincipal_LFunction_compact_le χ hχ (by linarith)
    linarith
  have hdist : ‖s - c‖ ≤ 3 * r := by
    have h := norm_add_le (s - 1) (1 - c)
    have hc : ‖(1 : ℂ) - c‖ = 2 * r := by
      change ‖(1 : ℂ) - ((1 + 2 * r : ℝ) : ℂ)‖ = 2 * r
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
      norm_num [show (1 : ℝ) - (1 + 2 * r) = -(2 * r) by ring, abs_of_pos hr]
    rw [sub_add_sub_cancel, hc] at h
    linarith
  exact norm_le_small_power_of_two_disks (DirichletCharacter.differentiable_LFunction hχ)
    hr hrR hAc (by norm_num) (by exact_mod_cast (by omega : 1 ≤ q)) hε.le hscale
    hinner houter hdist (hdist.trans hrsmall)

theorem exists_nonprincipal_LFunction_one_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      2 ≤ q → χ ≠ 1 → ‖DirichletCharacter.LFunction χ 1‖ ≤ K * (q : ℝ) ^ ε := by
  obtain ⟨r, K, hr, hK, h⟩ := exists_nonprincipal_small_power_disk hε
  refine ⟨K, hK, ?_⟩
  intro q inst χ hq hχ
  exact h q χ hq hχ 1 (by simpa using hr.le)

end Chen
