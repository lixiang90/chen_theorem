import ChenTheorem.Lemma6.LFunctionChangeLevelLogDerivative
import ChenTheorem.Lemma6.ZetaRealLogDerivativeBound

open Set Metric
open scoped Topology

namespace Chen

theorem norm_principal_logDeriv_sub_zeta_le {q : ℕ} [NeZero q]
    (s : ℂ) (hs : 1 < s.re) :
    ‖logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s -
      logDeriv riemannZeta s‖ ≤ Real.log q := by
  simpa only [DirichletCharacter.changeLevel_one, DirichletCharacter.LFunction_modOne_eq]
    using norm_logDeriv_LFunction_changeLevel_sub_le (Nat.one_dvd q)
      (1 : DirichletCharacter ℂ 1) s hs

theorem exists_zeta_complex_logDeriv_pole_bound :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ s : ℂ, ‖s - 1‖ < δ → s ≠ 1 →
      ‖logDeriv riemannZeta s + (s - 1)⁻¹‖ ≤ C := by
  obtain ⟨U, hU, B, hB⟩ := riemannZetaLogDerivResidue
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ, max B 1, hδ, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro s hs hsne
  have hsU : s ∈ U := hδU (by simpa only [mem_ball, dist_eq_norm] using hs)
  have hb := hB (mem_image_of_mem _ (show s ∈ U \ {1} from ⟨hsU, hsne⟩))
  change ‖-(deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹‖ ≤ B at hb
  have he : -(deriv riemannZeta s / riemannZeta s) - (s - 1)⁻¹ =
      -(logDeriv riemannZeta s + (s - 1)⁻¹) := by rw [logDeriv_apply]; ring
  rw [he, norm_neg] at hb
  exact hb.trans (le_max_left _ _)

theorem exists_principal_complex_logDeriv_pole_bound :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (q : ℕ) [NeZero q] (s : ℂ),
      1 < s.re → ‖s - 1‖ < δ →
      ‖logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s +
        (s - 1)⁻¹‖ ≤ C + Real.log q := by
  obtain ⟨δ, C, hδ, hC, hz⟩ := exists_zeta_complex_logDeriv_pole_bound
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro q inst s hs hsδ
  have hsne : s ≠ 1 := by intro he; rw [he] at hs; norm_num at hs
  have h1 := norm_principal_logDeriv_sub_zeta_le (q := q) s hs
  have h2 := hz s hsδ hsne
  calc
    _ = ‖(logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s -
        logDeriv riemannZeta s) + (logDeriv riemannZeta s + (s - 1)⁻¹)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (by linarith)

end Chen
