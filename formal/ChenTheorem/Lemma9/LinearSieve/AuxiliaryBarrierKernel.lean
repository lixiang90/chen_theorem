import ChenTheorem.Lemma9.LinearSieve.AuxiliaryBarrierPhase

namespace Chen.LinearSieve

theorem log_unit_difference_le (s : ℝ) (hs : 2 ≤ s) :
    Real.log s - Real.log (s - 1) ≤ 2 / s := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < s - 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hs0 ht0)
  rw [Real.log_div hs0.ne' ht0.ne'] at h
  have he : s / (s - 1) - 1 = 1 / (s - 1) := by field_simp; ring
  rw [he] at h
  exact h.trans ((div_le_div_iff₀ ht0 hs0).mpr (by linarith))

theorem auxiliaryAdjoint_unit_upper (s u : ℝ)
    (hs : 4 ≤ s) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    auxiliaryAdjoint (s + u) ≤ auxiliaryAdjoint s * Real.exp (4 * u / s) := by
  have hs0 : 0 < s := by linarith
  have hq : 0 < auxiliaryAdjoint s := auxiliaryAdjoint_pos s (by linarith)
  have hqlo : s ^ 2 ≤ 2 * auxiliaryAdjoint s := by
    dsimp [auxiliaryAdjoint]
    nlinarith
  have hd : auxiliaryAdjoint (s + u) ≤ auxiliaryAdjoint s + 2 * s * u := by
    dsimp [auxiliaryAdjoint]
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hu1)]
  have hm : 2 * s * u ≤ auxiliaryAdjoint s * (4 * u / s) := by
    rw [← mul_div_assoc, le_div_iff₀ hs0]
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hqlo)]
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (4 * u / s)) hq.le
  nlinarith

theorem auxiliaryBarrierPhase_unit_lower (a C s u : ℝ)
    (ha : 0 ≤ a) (hs : 4 ≤ s) (hu : 0 ≤ u) :
    (auxiliaryBarrierSlope a C s - 2 * a / s) * u ≤
      auxiliaryBarrierPhase a C (s - 1 + u) - auxiliaryBarrierPhase a C (s - 1) := by
  have hi := (auxiliaryBarrierPhase_increment_bounds a C (s - 1) (s - 1 + u)
    ha (by linarith) (by linarith)).1
  simp only [add_sub_cancel_left] at hi
  have hlog := mul_le_mul_of_nonneg_left (log_unit_difference_le s (by linarith)) ha
  have he : a * (2 / s) = 2 * a / s := by ring
  rw [he] at hlog
  have hsl : auxiliaryBarrierSlope a C s - 2 * a / s ≤ auxiliaryBarrierSlope a C (s - 1) := by
    dsimp [auxiliaryBarrierSlope]
    nlinarith
  exact (mul_le_mul_of_nonneg_right hsl hu).trans hi

/-- An exponential upper envelope for the weighted kernel in the scalar
pairing, uniform in the linear coefficient of the barrier phase. -/
theorem auxiliaryBarrier_kernel_upper (a C s u : ℝ)
    (ha : 0 ≤ a) (hs : 4 ≤ s) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    auxiliaryAdjoint (s + u) *
        Real.exp (auxiliaryBarrierPhase a C (s - 1) - auxiliaryBarrierPhase a C (s - 1 + u)) ≤
      auxiliaryAdjoint s *
        Real.exp (-(auxiliaryBarrierSlope a C s - (2 * a + 4) / s) * u) := by
  have hq := auxiliaryAdjoint_unit_upper s u hs hu hu1
  have hp := auxiliaryBarrierPhase_unit_lower a C s u ha hs hu
  have he := Real.exp_le_exp.mpr (show
      auxiliaryBarrierPhase a C (s - 1) - auxiliaryBarrierPhase a C (s - 1 + u) ≤
        -(auxiliaryBarrierSlope a C s - 2 * a / s) * u by linarith)
  have hm := _root_.mul_le_mul hq he (Real.exp_pos _).le
    (mul_nonneg (auxiliaryAdjoint_pos s (by linarith)).le (Real.exp_pos _).le)
  calc
    _ ≤ (auxiliaryAdjoint s * Real.exp (4 * u / s)) *
        Real.exp (-(auxiliaryBarrierSlope a C s - 2 * a / s) * u) := hm
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end Chen.LinearSieve
