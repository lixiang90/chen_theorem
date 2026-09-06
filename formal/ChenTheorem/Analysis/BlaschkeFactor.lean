import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.LogDeriv

open Set Metric
open scoped ComplexConjugate

namespace Chen

noncomputable def blaschkeFactor (R : ℝ) (w z : ℂ) : ℂ :=
  (R : ℂ) * (z - w) / ((R : ℂ) ^ 2 - conj w * z)

theorem blaschkeFactor_eq_inv_canonicalFactor (R : ℝ) (w z : ℂ) :
    blaschkeFactor R w z = (Complex.canonicalFactor R w z)⁻¹ := by
  simp [blaschkeFactor, Complex.canonicalFactor, inv_div]

theorem blaschke_denominator_ne_zero {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 R) :
    (R : ℂ) ^ 2 - conj w * z ≠ 0 := by
  have hwR : ‖w‖ < R := by simpa using hw
  have hzR : ‖z‖ ≤ R := by simpa using hz
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg w) hwR
  have hp : ‖conj w * z‖ < R ^ 2 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [mul_le_mul_of_nonneg_left hzR (norm_nonneg w)]
  intro he
  have he' := congrArg norm (sub_eq_zero.mp he)
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] at he'
  linarith

theorem analyticOnNhd_blaschkeFactor {R : ℝ} {w : ℂ} (hw : w ∈ ball 0 R) :
    AnalyticOnNhd ℂ (blaschkeFactor R w) (closedBall 0 R) := by
  intro z hz
  unfold blaschkeFactor
  fun_prop (disch := exact blaschke_denominator_ne_zero hw hz)

theorem norm_blaschkeFactor_on_sphere {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ sphere 0 R) : ‖blaschkeFactor R w z‖ = 1 := by
  rw [blaschkeFactor_eq_inv_canonicalFactor, norm_inv,
    Complex.norm_canonicalFactor_eval_circle_eq_one hw hz, inv_one]

/-- The maximum principle on a disk, with the closed-ball analyticity
interface used by finite zero factorizations. -/
theorem norm_le_of_analyticOnNhd_closedBall {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) {z : ℂ} (hz : z ∈ closedBall c R) :
    ‖f z‖ ≤ M := by
  have hd : DiffContOnCl ℂ f (ball c R) := by
    apply DifferentiableOn.diffContOnCl
    simpa only [closure_ball _ hR.ne'] using hf.differentiableOn
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
  · simpa only [frontier_ball _ hR.ne'] using hb
  · simpa only [closure_ball _ hR.ne'] using hz

theorem norm_blaschkeFactor_le_one {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 R) : ‖blaschkeFactor R w z‖ ≤ 1 := by
  apply norm_le_of_analyticOnNhd_closedBall (pos_of_mem_ball hw) (analyticOnNhd_blaschkeFactor hw)
    (fun u hu => (norm_blaschkeFactor_on_sphere hw hu).le) hz

theorem blaschkeFactor_ne_zero {R : ℝ} {w z : ℂ} (hw : w ∈ ball 0 R)
    (hz : z ∈ closedBall 0 R) (hzw : z ≠ w) : blaschkeFactor R w z ≠ 0 := by
  unfold blaschkeFactor
  exact div_ne_zero (mul_ne_zero (by exact_mod_cast (pos_of_mem_ball hw).ne')
    (sub_ne_zero.mpr hzw)) (blaschke_denominator_ne_zero hw hz)

end Chen
