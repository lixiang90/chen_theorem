import ChenTheorem.Lemma6.LFunctionEulerBounds
import ChenTheorem.Analysis.ZeroFreeLogDerivative

open Set Metric

namespace Chen

/-- A primitive L-function has an explicit logarithmic-derivative estimate
in the three-quarter subdisk of a zero-free disk centered just to the right of one.
Only the zero-free disk remains an assumption: the growth and the lower
bound at its center are supplied by proved arithmetic estimates. -/
theorem norm_LFunction_logDeriv_le_of_nonvanishing_ball
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) (c : ℂ) (R : ℝ)
    (hR : 0 < R) (hRsmall : R ≤ 1 / 4)
    (hc : 1 + R / 4 ≤ c.re) (hc2 : c.re ≤ 2)
    (hne : ∀ w ∈ ball c R, DirichletCharacter.LFunction χ w ≠ 0)
    (z : ℂ) (hz : dist z c ≤ 3 * R / 4) :
    ‖deriv (DirichletCharacter.LFunction χ) z / DirichletCharacter.LFunction χ z‖ ≤
      224 * Real.log (48 * Real.sqrt q * Real.log (2 * q) * (‖c‖ + R) / R + 1) / R := by
  have hχne : χ ≠ 1 := by
    intro hχone
    have hcondOne : χ.conductor = 1 := DirichletCharacter.eq_one_iff_conductor_eq_one.mp hχone
    rw [DirichletCharacter.isPrimitive_def] at hχ
    omega
  let B : ℝ := 3 * Real.sqrt q * Real.log (2 * q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog : 0 < Real.log (2 * (q : ℝ)) := Real.log_pos (by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith)
  have hB : 0 < B := by dsimp [B]; positivity
  have hcre : 1 < c.re := by linarith
  have hanchor : R / 8 ≤ ‖DirichletCharacter.LFunction χ c‖ := by
    apply le_trans _ (norm_LFunction_euler_lower χ c hcre)
    apply (le_div_iff₀ (show 0 < c.re by linarith)).mpr
    nlinarith
  have hgrowth : ∀ w ∈ ball c R, ‖DirichletCharacter.LFunction χ w‖ ≤ 2 * B * (‖c‖ + R) := by
    intro w hw
    have hdist : ‖w - c‖ < R := by simpa only [mem_ball, dist_eq_norm] using hw
    have hrew : (1 / 2 : ℝ) ≤ w.re := by
      have hreal := Complex.abs_re_le_norm (w - c)
      rw [Complex.sub_re] at hreal
      have := (abs_le.mp hreal).1
      linarith
    have hn : ‖w‖ ≤ ‖c‖ + R := by
      have htriangle' : ‖w‖ ≤ ‖w - c‖ + ‖c‖ := norm_le_norm_sub_add w c
      linarith
    apply (norm_LFunction_le_of_re_pos hχ hq (by linarith : 0 < w.re)).trans
    change B * ‖w‖ / w.re ≤ _
    apply (div_le_iff₀ (show 0 < w.re by linarith)).mpr
    have hnormpos : 0 ≤ ‖c‖ + R := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hn hB.le,
      mul_le_mul_of_nonneg_left hrew (mul_nonneg hB.le hnormpos)]
  let A : ℝ := 16 * B * (‖c‖ + R) / R
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 < Real.log (A + 1) := Real.log_pos (by linarith)
  have hbound : ∀ w ∈ ball c R, ‖DirichletCharacter.LFunction χ w‖ ≤
      Real.exp (Real.log (A + 1)) * ‖DirichletCharacter.LFunction χ c‖ := by
    intro w hw
    rw [Real.exp_log (by linarith : 0 < A + 1)]
    apply (hgrowth w hw).trans
    have ha : 2 * B * (‖c‖ + R) ≤ A * ‖DirichletCharacter.LFunction χ c‖ := by
      dsimp [A]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hR).mpr
      nlinarith [mul_le_mul_of_nonneg_left hanchor (by positivity : 0 ≤ 16 * B * (‖c‖ + R))]
    nlinarith [norm_nonneg (DirichletCharacter.LFunction χ c)]
  have h := norm_logDeriv_le_of_nonvanishing_ball (DirichletCharacter.LFunction χ) c R
    (Real.log (A + 1)) hR hM (DirichletCharacter.differentiable_LFunction hχne).differentiableOn
    hne hbound z hz
  convert h using 1
  dsimp [A, B]
  congr 3
  ring

end Chen
