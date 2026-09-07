import Submission.ChenTheorem.Lemma6.ZetaHighLogDerivativeBound
import Submission.ChenTheorem.Lemma6.PrincipalLogDerivativeBound

set_option autoImplicit true
open Set Metric

namespace Chen

theorem exists_zeta_logDeriv_compact_bound (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℝ, 0 < B ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 3 / 2 → ρ ≤ |t| → |t| ≤ 1 →
      ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B := by
  let K : Set ℂ := closedBall 0 3 ∩ ({s | 1 ≤ s.re} ∩ {s | ρ ≤ |s.im|})
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 3).inter_right
    ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le continuous_const Complex.continuous_im.abs))
  have hcont : ContinuousOn (logDeriv riemannZeta) K := by
    intro s hs
    have hsne : s ≠ 1 := by
      intro he
      have h := hs.2.2
      rw [he] at h
      norm_num at h
      linarith
    have ha := analyticOn_riemannZeta s hsne
    change ContinuousWithinAt (fun z => deriv riemannZeta z / riemannZeta z) K s
    exact (ha.deriv.continuousAt.div ha.continuousAt
      (riemannZeta_ne_zero_of_one_le_re hs.2.1)).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcont.norm
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro σ t hσ hσ' ht ht'
  have hsK : (σ : ℂ) + (t : ℂ) * Complex.I ∈ K := by
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff]
      have h := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
        abs_of_pos (by linarith : 0 < σ)] at h
      linarith
    · simpa using hσ
    · simpa using ht
  exact (hB (mem_image_of_mem _ hsK)).trans (le_max_left _ _)

theorem exists_zeta_logDeriv_re_ge_away_pole (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 3 / 2 → ρ ≤ |t| →
      -(C * Real.log (|t| + 2)) ≤
        (logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  obtain ⟨B, hB, hb⟩ := exists_zeta_logDeriv_compact_bound ρ hρ
  refine ⟨60000 + 2 * B, by positivity, ?_⟩
  intro σ t hσ hσ' ht
  have hL := height_log_ge_half t
  by_cases ht' : 1 ≤ |t|
  · have h := riemannZeta_logDeriv_re_ge_high σ t hσ hσ' ht'
    nlinarith
  · have hnorm := hb σ t hσ.le hσ' ht (le_of_not_ge ht')
    have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
    nlinarith

theorem exists_principal_logDeriv_re_ge_away_pole (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 2 ≤ q → ∀ σ t : ℝ,
      1 < σ → σ ≤ 3 / 2 → ρ ≤ |t| →
      -(C * Real.log ((q : ℝ) * (|t| + 2))) ≤
        (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
          ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  obtain ⟨C, hC, hz⟩ := exists_zeta_logDeriv_re_ge_away_pole ρ hρ
  refine ⟨C + 1, by positivity, ?_⟩
  intro q inst hq σ t hσ hσ' ht
  have h1 := hz σ t hσ hσ' ht
  have h2 := norm_principal_logDeriv_sub_zeta_le (q := q)
    ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using hσ)
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans h2)).1
  rw [Complex.sub_re] at hr
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hA : 0 < |t| + 2 := by positivity
  have hlogt : Real.log (|t| + 2) ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log hA
    nlinarith
  have hlogq : Real.log q ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
    apply Real.log_le_log (by linarith : (0 : ℝ) < q)
    nlinarith [abs_nonneg t]
  nlinarith

end Chen
