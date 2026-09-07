import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliarySumPairing

set_option autoImplicit true
open Set MeasureTheory

namespace Chen.LinearSieve

theorem monotoneOn_auxiliaryAdjoint : MonotoneOn auxiliaryAdjoint (Ici 2) := by
  intro s hs t ht hst
  change 2 ≤ s at hs
  change 2 ≤ t at ht
  dsimp [auxiliaryAdjoint]
  nlinarith [mul_nonneg (sub_nonneg.mpr hst) (show 0 ≤ t + s - 2 by linarith)]

theorem auxiliaryErrorSum_shift_pairing_bound (s : ℝ) (hs : 3 < s) :
    s * auxiliaryAdjoint s * auxiliaryErrorSum s ≤
      auxiliaryAdjoint (s + 1) * auxiliaryErrorSum (s - 1) := by
  rw [auxiliaryErrorSum_pairing_zero s hs]
  have hab : s - 1 ≤ s := by linarith
  have hc : ContinuousOn (fun t => auxiliaryAdjoint (t + 1) * auxiliaryErrorSum t)
      (Icc (s - 1) s) := by
    apply ContinuousOn.mul _ (continuousOn_auxiliaryErrorSum.mono
      (by intro t ht; change 1 < t; linarith [ht.1]))
    unfold auxiliaryAdjoint
    fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab (hc.intervalIntegrable_of_Icc hab)
    (intervalIntegrable_const (c := auxiliaryAdjoint (s + 1) * auxiliaryErrorSum (s - 1)))
    (show ∀ t ∈ Icc (s - 1) s,
      auxiliaryAdjoint (t + 1) * auxiliaryErrorSum t ≤
        auxiliaryAdjoint (s + 1) * auxiliaryErrorSum (s - 1) from by
      intro t ht
      exact _root_.mul_le_mul
        (monotoneOn_auxiliaryAdjoint (by change 2 ≤ t + 1; linarith [ht.1])
          (by change 2 ≤ s + 1; linarith) (by linarith [ht.2]))
        (antitoneOn_auxiliaryErrorSum (by change 1 < s - 1; linarith)
          (by change 1 < t; linarith [ht.1]) ht.1)
        (auxiliaryErrorSum_pos t (by linarith [ht.1])).le
        (auxiliaryAdjoint_pos (s + 1) (by linarith)).le)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_sub_cancel, one_mul]
    using hi

theorem auxiliaryErrorSum_shift_lower (s : ℝ) (hs : 3 < s) :
    s * auxiliaryErrorSum s ≤ 3 * auxiliaryErrorSum (s - 1) := by
  have h := auxiliaryErrorSum_shift_pairing_bound s hs
  have hq : auxiliaryAdjoint (s + 1) ≤ 3 * auxiliaryAdjoint s := by
    dsimp [auxiliaryAdjoint]
    nlinarith
  have hp := auxiliaryAdjoint_pos s (by linarith)
  have hn := (auxiliaryErrorSum_pos (s - 1) (by linarith)).le
  have hm := mul_le_mul_of_nonneg_right hq hn
  nlinarith

/-- A quantitative version of the elementary shift bound, with coefficient
approaching one. It does not assert the sharper logarithmic shift estimate. -/
theorem auxiliaryErrorSum_shift_lower_sharp (s : ℝ) (hs : 4 ≤ s) :
    s * auxiliaryErrorSum s ≤ (1 + 4 / s) * auxiliaryErrorSum (s - 1) := by
  have h := auxiliaryErrorSum_shift_pairing_bound s (by linarith)
  have hs0 : 0 < s := by linarith
  have hp := auxiliaryAdjoint_pos s (by linarith)
  have hn := (auxiliaryErrorSum_pos (s - 1) (by linarith)).le
  have hq : s * auxiliaryAdjoint (s + 1) ≤ (s + 4) * auxiliaryAdjoint s := by
    dsimp [auxiliaryAdjoint]
    nlinarith [sq_nonneg (s - 4)]
  have h' := mul_le_mul_of_nonneg_left h hs0.le
  have hq' := mul_le_mul_of_nonneg_right hq hn
  have he : (1 + 4 / s) * auxiliaryErrorSum (s - 1) =
      (s + 4) * auxiliaryErrorSum (s - 1) / s := by
    field_simp
  rw [he, le_div_iff₀ hs0]
  nlinarith

theorem hasDerivAt_exp_third_sq_mul_auxiliaryErrorSum (s : ℝ) (hs : 3 < s) :
    HasDerivAt (fun t => Real.exp (t / 3) * (t ^ 2 * auxiliaryErrorSum t))
      (Real.exp (s / 3) * s *
        (s / 3 * auxiliaryErrorSum s - auxiliaryErrorSum (s - 1))) s := by
  apply ((((hasDerivAt_id s).div_const 3).exp).mul
    (hasDerivAt_sq_mul_auxiliaryErrorSum s hs)).congr_deriv
  dsimp
  ring

theorem antitoneOn_exp_third_sq_mul_auxiliaryErrorSum :
    AntitoneOn (fun s => Real.exp (s / 3) * (s ^ 2 * auxiliaryErrorSum s)) (Ici 4) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 4)
  · apply ContinuousOn.mul (by fun_prop)
    exact (continuousOn_id.pow 2).mul (continuousOn_auxiliaryErrorSum.mono
      (by intro s hs; change 1 < s; linarith [show 4 ≤ s from hs]))
  · intro s hs
    rw [interior_Ici] at hs
    exact (hasDerivAt_exp_third_sq_mul_auxiliaryErrorSum s
      (by linarith [show 4 < s from hs])).hasDerivWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    have h := auxiliaryErrorSum_shift_lower s (by linarith [show 4 < s from hs])
    apply mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.exp_pos _).le (by linarith [show 4 < s from hs]))
    linarith

theorem auxiliaryErrorSum_exponential_comparison (s t : ℝ) (hs : 4 ≤ s) (hst : s ≤ t) :
    auxiliaryErrorSum t ≤ Real.exp (-(t - s) / 3) * auxiliaryErrorSum s := by
  have h := antitoneOn_exp_third_sq_mul_auxiliaryErrorSum hs (hs.trans hst) hst
  have ht0 : 0 < t := by linarith
  have hn := (auxiliaryErrorSum_pos t (by linarith)).le
  have hsq : s ^ 2 ≤ t ^ 2 := by nlinarith
  have h' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hn)
    (Real.exp_pos (t / 3)).le
  have hcancel : Real.exp (t / 3) * auxiliaryErrorSum t ≤
      Real.exp (s / 3) * auxiliaryErrorSum s := by
    nlinarith [sq_pos_of_pos (show 0 < s by linarith)]
  rw [mul_comm (Real.exp (t / 3)), ← le_div_iff₀ (Real.exp_pos (t / 3))] at hcancel
  convert! hcancel using 1
  rw [show -(t - s) / 3 = s / 3 - t / 3 by ring, Real.exp_sub]
  ring

end Chen.LinearSieve
