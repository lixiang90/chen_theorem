import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousAuxiliaryWeights
import Submission.ChenTheorem.Lemma9.LinearSieve.SieveParameter

set_option autoImplicit true
open Set MeasureTheory Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The basic logarithmic error scale used by the quantitative depth
comparison. Additional uniformity factors have not been included here. -/
noncomputable def auxiliaryErrorScale (δ D s : ℝ) (H : ℝ → ℝ) : ℝ :=
  (Real.log D) ^ (-δ) * s * H s

theorem log_child_level_eq (D p : ℝ) (hD : 1 < D) (hp : 1 < p) :
    Real.log (D / p) = Real.log D *
      ((sieveParameter D p - 1) / sieveParameter D p) := by
  have hD0 : D ≠ 0 := by linarith
  have hp0 : p ≠ 0 := by linarith
  have hlD : Real.log D ≠ 0 := (Real.log_pos hD).ne'
  have hlp : Real.log p ≠ 0 := (Real.log_pos hp).ne'
  rw [Real.log_div hD0 hp0, sieveParameter]
  field_simp

theorem log_child_level_rpow (δ D p : ℝ) (hD : 1 < D) (hp : 1 < p)
    (hs : 1 < sieveParameter D p) :
    (Real.log (D / p)) ^ (-δ) = (Real.log D) ^ (-δ) *
      (sieveParameter D p / (sieveParameter D p - 1)) ^ δ := by
  have hs0 : 0 < sieveParameter D p := by linarith
  have hs1 : 0 < sieveParameter D p - 1 := by linarith
  rw [log_child_level_eq D p hD hp,
    Real.mul_rpow (Real.log_pos hD).le (div_pos hs1 hs0).le]
  congr 1
  rw [Real.rpow_neg_eq_inv_rpow]
  congr 1
  field_simp

theorem auxiliaryErrorScale_child (δ D p : ℝ) (H : ℝ → ℝ)
    (hD : 1 < D) (hp : 1 < p) (hs : 1 < sieveParameter D p) :
    auxiliaryErrorScale δ (D / p) (sieveParameter (D / p) p) H =
      (Real.log D) ^ (-δ) * childAuxiliaryWeight δ (sieveParameter D p) *
        H (sieveParameter D p - 1) := by
  rw [auxiliaryErrorScale, sieveParameter_div_self D p (by linarith) hp,
    log_child_level_rpow δ D p hD hp hs]
  unfold childAuxiliaryWeight
  ring

theorem parameter_integral_auxiliaryErrorScale_lower_le (δ D s b : ℝ)
    (hδ : δ ≤ 1) (hD : 1 < D) (hs : 3 ≤ s) (hsb : s ≤ b) :
    (1 / s) * (∫ t in s..b, (Real.log D) ^ (-δ) *
      (childAuxiliaryWeight δ t * lowerAuxiliaryError (t - 1))) ≤
        auxiliaryErrorScale δ D s upperAuxiliaryError := by
  rw [intervalIntegral.integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (parameter_integral_childAuxiliaryWeight_lower_le δ s b hδ hs hsb)
    (Real.rpow_nonneg (Real.log_pos hD).le (-δ))
  dsimp [auxiliaryErrorScale]
  nlinarith

theorem parameter_integral_auxiliaryErrorScale_upper_le (δ D s b : ℝ)
    (hδ : δ ≤ 1) (hD : 1 < D) (hs : 2 < s) (hsb : s ≤ b) :
    (1 / s) * (∫ t in s..b, (Real.log D) ^ (-δ) *
      (childAuxiliaryWeight δ t * upperAuxiliaryError (t - 1))) ≤
        auxiliaryErrorScale δ D s lowerAuxiliaryError := by
  rw [intervalIntegral.integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (parameter_integral_childAuxiliaryWeight_upper_le δ s b hδ hs hsb)
    (Real.rpow_nonneg (Real.log_pos hD).le (-δ))
  dsimp [auxiliaryErrorScale]
  nlinarith

theorem tendsto_auxiliaryErrorScale_zero (δ s : ℝ) (H : ℝ → ℝ) (hδ : 0 < δ) :
    Tendsto (fun D => auxiliaryErrorScale δ D s H) atTop (𝓝 0) := by
  have h := ((tendsto_rpow_neg_atTop hδ).comp Real.tendsto_log_atTop).mul_const s
  simpa only [auxiliaryErrorScale, zero_mul, Function.comp_def] using h.mul_const (H s)

theorem auxiliaryErrorScale_nonneg (δ D s : ℝ) (H : ℝ → ℝ)
    (hD : 1 < D) (hs : 0 ≤ s) (hH : 0 ≤ H s) :
    0 ≤ auxiliaryErrorScale δ D s H :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg (Real.log_pos hD).le (-δ)) hs) hH

end Chen.LinearSieve
