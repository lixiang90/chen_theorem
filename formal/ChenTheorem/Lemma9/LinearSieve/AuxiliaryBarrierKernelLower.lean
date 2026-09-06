import ChenTheorem.Lemma9.LinearSieve.AuxiliaryBarrierKernel

namespace Chen.LinearSieve

theorem auxiliaryAdjoint_half_lower (s u : ℝ)
    (hs : 4 ≤ s) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    auxiliaryAdjoint s * Real.exp (u / s) ≤ auxiliaryAdjoint (s + u) := by
  have hs0 : 0 < s := by linarith
  have hp := auxiliaryAdjoint_pos s (by linarith)
  have hpu := auxiliaryAdjoint_pos (s + u) (by linarith)
  have hupper : auxiliaryAdjoint (s + u) ≤ s ^ 2 := by
    dsimp [auxiliaryAdjoint]
    nlinarith [mul_nonneg hs0.le (show 0 ≤ 1 - 2 * u by linarith),
      mul_nonneg hu (sub_nonneg.mpr hu1)]
  have hlower : s * u ≤ auxiliaryAdjoint (s + u) - auxiliaryAdjoint s := by
    dsimp [auxiliaryAdjoint]
    nlinarith [mul_nonneg hu (show 0 ≤ s - 2 by linarith)]
  have hfrac : u / s ≤ (auxiliaryAdjoint (s + u) - auxiliaryAdjoint s) /
      auxiliaryAdjoint (s + u) := by
    apply (div_le_div_iff₀ hs0 hpu).mpr
    nlinarith [mul_le_mul_of_nonneg_left hupper hu,
      mul_le_mul_of_nonneg_left hlower hs0.le]
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hpu hp)
  have he : 1 - (auxiliaryAdjoint (s + u) / auxiliaryAdjoint s)⁻¹ =
      (auxiliaryAdjoint (s + u) - auxiliaryAdjoint s) / auxiliaryAdjoint (s + u) := by
    field_simp
  rw [he] at hlog
  have hexp := Real.exp_le_exp.mpr (hfrac.trans hlog)
  rw [Real.exp_log (div_pos hpu hp)] at hexp
  have h := (le_div_iff₀ hp).mp hexp
  simpa only [mul_comm] using h

theorem auxiliaryBarrierPhase_half_upper (a C s u : ℝ)
    (ha : 0 ≤ a) (hs : 4 ≤ s) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    auxiliaryBarrierPhase a C (s - 1 + u) - auxiliaryBarrierPhase a C (s - 1) ≤
      (auxiliaryBarrierSlope a C s - a / (2 * s)) * u := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < s - 1 + u := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos ht0 hs0)
  rw [Real.log_div ht0.ne' hs0.ne'] at hlog
  have he : (s - 1 + u) / s - 1 = (u - 1) / s := by field_simp; ring
  rw [he] at hlog
  have hfrac := div_le_div_of_nonneg_right (show u - 1 ≤ -(1 / 2 : ℝ) by linarith) hs0.le
  have h := mul_le_mul_of_nonneg_left (hlog.trans hfrac) ha
  have hsl : auxiliaryBarrierSlope a C (s - 1 + u) ≤
      auxiliaryBarrierSlope a C s - a / (2 * s) := by
    have heq : a * (-(1 / 2 : ℝ) / s) = -a / (2 * s) := by ring
    rw [heq] at h
    rw [neg_div] at h
    dsimp [auxiliaryBarrierSlope]
    nlinarith
  have hi := (auxiliaryBarrierPhase_increment_bounds a C (s - 1) (s - 1 + u)
    ha (by linarith) (by linarith)).2
  simp only [add_sub_cancel_left] at hi
  exact hi.trans (mul_le_mul_of_nonneg_right hsl hu)

/-- The first half of the unit interval suffices for the upper logarithmic
barrier. Its phase increment gains a term of order `1/s`. -/
theorem auxiliaryBarrier_kernel_lower (a C s u : ℝ)
    (ha : 0 ≤ a) (hs : 4 ≤ s) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    auxiliaryAdjoint s *
        Real.exp (-(auxiliaryBarrierSlope a C s - (1 + a / 2) / s) * u) ≤
      auxiliaryAdjoint (s + u) *
        Real.exp (auxiliaryBarrierPhase a C (s - 1) - auxiliaryBarrierPhase a C (s - 1 + u)) := by
  have hq := auxiliaryAdjoint_half_lower s u hs hu hu1
  have hp := auxiliaryBarrierPhase_half_upper a C s u ha hs hu hu1
  have he := Real.exp_le_exp.mpr (show
      -(auxiliaryBarrierSlope a C s - a / (2 * s)) * u ≤
        auxiliaryBarrierPhase a C (s - 1) - auxiliaryBarrierPhase a C (s - 1 + u) by linarith)
  have hm := _root_.mul_le_mul hq he (Real.exp_pos _).le
    (auxiliaryAdjoint_pos (s + u) (by linarith)).le
  calc
    _ = (auxiliaryAdjoint s * Real.exp (u / s)) *
        Real.exp (-(auxiliaryBarrierSlope a C s - a / (2 * s)) * u) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := hm

end Chen.LinearSieve
