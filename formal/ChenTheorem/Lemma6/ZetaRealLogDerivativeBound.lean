import ChenTheorem.Analysis.PNT.ZetaBounds

open Set Metric
open scoped Topology

namespace Chen

theorem exists_zeta_real_logDeriv_pole_bound :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + C := by
  obtain ⟨U, hU, B, hB⟩ := riemannZetaLogDerivResidue
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ, max B 1, hδ, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro σ hσ hσδ
  have hsU : (σ : ℂ) ∈ U := by
    apply hδU
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < σ - 1)]
    linarith
  have hsne : (σ : ℂ) ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.one_re] at this
    linarith
  have hb := hB (mem_image_of_mem _ (show (σ : ℂ) ∈ U \ {1} from ⟨hsU, hsne⟩))
  change ‖-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)) - ((σ : ℂ) - 1)⁻¹‖ ≤ B at hb
  have hr := (Complex.re_le_norm _).trans (hb.trans (le_max_left B (1 : ℝ)))
  rw [Complex.sub_re, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_inv, Complex.ofReal_re] at hr
  rw [neg_div]
  rw [one_div]
  linarith

end Chen
