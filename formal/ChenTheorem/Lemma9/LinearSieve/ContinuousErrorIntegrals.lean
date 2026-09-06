import ChenTheorem.Lemma9.LinearSieve.ContinuousUpperSmooth

open Set MeasureTheory

namespace Chen.LinearSieve

theorem integral_shift_lowerContinuousError (s b : ℝ) (hs : 3 < s) (hsb : s ≤ b) :
    (∫ t in s..b, lowerContinuousError (t - 1)) =
      s * upperContinuousError s - b * upperContinuousError b := by
  have hc : ContinuousOn (fun t => lowerContinuousError (t - 1)) (Icc s b) :=
    continuousOn_lowerContinuousError.comp (continuousOn_id.sub continuousOn_const)
      (fun t ht => by change 2 ≤ t - 1; linarith [ht.1])
  have hi : IntervalIntegrable (fun t => lowerContinuousError (t - 1)) volume s b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hsb] using hc
  have hf : ContinuousOn (fun t => t * upperContinuousError t) (Icc s b) :=
    continuousOn_id.mul (continuousOn_upperContinuousError.mono
      (fun t ht => by change 1 < t; linarith [ht.1]))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsb hf
    (fun t ht => hasDerivAt_mul_upperContinuousError t (by linarith [ht.1])) hi.neg
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem integral_shift_upperContinuousError (s b : ℝ) (hs : 2 < s) (hsb : s ≤ b) :
    (∫ t in s..b, upperContinuousError (t - 1)) =
      s * lowerContinuousError s - b * lowerContinuousError b := by
  have hc : ContinuousOn (fun t => upperContinuousError (t - 1)) (Icc s b) :=
    continuousOn_upperContinuousError.comp (continuousOn_id.sub continuousOn_const)
      (fun t ht => by change 1 < t - 1; linarith [ht.1])
  have hi : IntervalIntegrable (fun t => upperContinuousError (t - 1)) volume s b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hsb] using hc
  have hf : ContinuousOn (fun t => t * lowerContinuousError t) (Icc s b) :=
    continuousOn_id.mul (continuousOn_lowerContinuousError.mono
      (fun t ht => by change 2 ≤ t; linarith [ht.1]))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsb hf
    (fun t ht => hasDerivAt_mul_lowerContinuousError t (by linarith [ht.1])) hi.neg
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- The actual lower error is an admissible integral kernel for the
upper recursion, with an explicit nonnegative tail discarded. -/
theorem parameter_integral_shift_lowerContinuousError_le (s b : ℝ)
    (hs : 3 < s) (hsb : s ≤ b) :
    (1 / s) * (∫ t in Ioc s b, lowerContinuousError (t - 1)) ≤ upperContinuousError s := by
  rw [← intervalIntegral.integral_of_le hsb, integral_shift_lowerContinuousError s b hs hsb]
  have hn := mul_nonneg (show 0 ≤ b by linarith)
    (upperContinuousError_bounds b (by linarith)).1
  have hs0 : 0 < s := by linarith
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hs0]
  nlinarith

theorem parameter_integral_shift_upperContinuousError_le (s b : ℝ)
    (hs : 2 < s) (hsb : s ≤ b) :
    (1 / s) * (∫ t in Ioc s b, upperContinuousError (t - 1)) ≤ lowerContinuousError s := by
  rw [← intervalIntegral.integral_of_le hsb, integral_shift_upperContinuousError s b hs hsb]
  have hn := mul_nonneg (show 0 ≤ b by linarith)
    (lowerContinuousError_bounds b (by linarith)).1
  have hs0 : 0 < s := by linarith
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hs0]
  nlinarith

end Chen.LinearSieve
