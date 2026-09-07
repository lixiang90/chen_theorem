import Submission.ChenTheorem.Analysis.AnalyticZeroFactorization
import Submission.ChenTheorem.Analysis.ZeroFreeLogDerivative

set_option autoImplicit true
open Set Metric MeromorphicOn

namespace Chen

/-- Removing the interior zeros preserves the boundary norm and increases
the modulus at the center. The analytic remainder inherits the original bound. -/
theorem exists_bounded_analytic_zeroFree_factor {f : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    (hb : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ M) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ ball 0 R, g z ≠ 0) ∧
      EqOn f (fun z => diskBlaschkeProduct f R z * g z) (closedBall 0 R) ∧
      (∀ z ∈ closedBall 0 R, ‖g z‖ ≤ M) ∧ ‖f 0‖ ≤ ‖g 0‖ := by
  obtain ⟨g, hg, hne, he⟩ := exists_analytic_blaschke_factorization hR hf h0
  have hfin := hf.meromorphicOn.divisor_ball_support_finite
  have hboundary : ∀ z ∈ sphere 0 R, ‖g z‖ = ‖f z‖ := by
    intro z hz
    rw [he (sphere_subset_closedBall hz), norm_mul,
      norm_diskBlaschkeProduct_on_sphere f R hfin hz, one_mul]
  refine ⟨g, hg, hne, he, ?_, ?_⟩
  · intro z hz
    exact norm_le_of_analyticOnNhd_closedBall hR hg
      (fun w hw => (hboundary w hw).trans_le (hb w hw)) hz
  · have hmem : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
    rw [he hmem, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (norm_diskBlaschkeProduct_le_one f R hfin hmem)

/-- A boundary growth estimate gives a quantitative logarithmic-derivative
bound for the analytic zero-free remainder of the finite Blaschke factorization. -/
theorem exists_analytic_factor_with_logDeriv_bound {f : ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hB : 0 < B) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h0 : f 0 ≠ 0) (hb : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ Real.exp B * ‖f 0‖) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ ball 0 R, g z ≠ 0) ∧
      EqOn f (fun z => diskBlaschkeProduct f R z * g z) (closedBall 0 R) ∧
      ∀ z : ℂ, ‖z‖ ≤ 3 * R / 4 → ‖deriv g z / g z‖ ≤ 224 * B / R := by
  obtain ⟨g, hg, hne, he, hbound, hanchor⟩ := exists_bounded_analytic_zeroFree_factor hR hf h0 hb
  refine ⟨g, hg, hne, he, ?_⟩
  intro z hz
  apply norm_logDeriv_le_of_nonvanishing_ball g 0 R B hR hB
    (hg.differentiableOn.mono ball_subset_closedBall) hne
  · intro w hw
    exact (hbound w (ball_subset_closedBall hw)).trans
      (mul_le_mul_of_nonneg_left hanchor (Real.exp_pos B).le)
  · simpa only [dist_zero_right] using hz

end Chen
