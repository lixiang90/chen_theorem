import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousPositivity
import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousAuxiliaryIntegrals

set_option autoImplicit true
open Set MeasureTheory

namespace Chen.LinearSieve

theorem antitoneOn_of_sq_mul_nonneg (a : ℝ) (H : ℝ → ℝ) (ha : 0 ≤ a)
    (hH : ∀ s ∈ Ioi a, 0 ≤ H s)
    (hanti : AntitoneOn (fun s => s ^ 2 * H s) (Ioi a)) :
    AntitoneOn H (Ioi a) := by
  intro s hs t ht hst
  have hs0 : 0 < s := lt_of_le_of_lt ha hs
  have ht0 : 0 < t := hs0.trans_le hst
  have hw := hanti hs ht hst
  have hp : s ^ 2 ≤ t ^ 2 := by nlinarith
  have hn := mul_nonneg (sub_nonneg.mpr hp) (hH t ht)
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hs0)).mp
  dsimp only at hw
  nlinarith

theorem antitoneOn_upperAuxiliaryError : AntitoneOn upperAuxiliaryError (Ioi 1) :=
  antitoneOn_of_sq_mul_nonneg 1 _ (by norm_num)
    (fun s hs => upperAuxiliaryError_nonneg s hs) antitoneOn_sq_mul_upperAuxiliaryError

theorem antitoneOn_lowerAuxiliaryError : AntitoneOn lowerAuxiliaryError (Ioi 0) :=
  antitoneOn_of_sq_mul_nonneg 0 _ le_rfl
    (fun s hs => lowerAuxiliaryError_nonneg s hs) antitoneOn_sq_mul_lowerAuxiliaryError

/-- A short terminal interval gives a lower bound in terms of the child
at its largest parameter on that interval. -/
theorem mul_shift_integral_lower_bound (a s ε : ℝ) (H : ℝ → ℝ)
    (hs0 : 0 ≤ s) (hs : a + 1 < s) (hε : 0 ≤ ε)
    (hcont : ContinuousOn H (Ioi a)) (hH : ∀ t ∈ Ioi a, 0 ≤ H t)
    (hanti : AntitoneOn H (Ioi a)) :
    ε * s * H (s + ε - 1) ≤ ∫ t in s..s + ε, t * H (t - 1) := by
  have hsb : s ≤ s + ε := by linarith
  have hHc : ContinuousOn (fun t => H (t - 1)) (Icc s (s + ε)) :=
    hcont.comp (continuousOn_id.sub continuousOn_const)
      (fun t ht => by change a < t - 1; linarith [ht.1])
  have hi : IntervalIntegrable (fun t => t * H (t - 1)) volume s (s + ε) :=
    (continuousOn_id.mul hHc).intervalIntegrable_of_Icc hsb
  have hm := intervalIntegral.integral_mono_on hsb
    (intervalIntegrable_const (c := s * H (s + ε - 1))) hi
    (show ∀ t ∈ Icc s (s + ε), s * H (s + ε - 1) ≤ t * H (t - 1) from by
      intro t ht
      have hp := hanti (show t - 1 ∈ Ioi a by change a < t - 1; linarith [ht.1])
        (show s + ε - 1 ∈ Ioi a by change a < s + ε - 1; linarith)
        (sub_le_sub_right ht.2 1)
      exact _root_.mul_le_mul ht.1 hp
        (hH _ (by change a < s + ε - 1; linarith)) (hs0.trans ht.1))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left, mul_assoc]
    using hm

theorem upperAuxiliaryError_lower_step (s ε : ℝ) (hs : 3 ≤ s) (hε : 0 ≤ ε) :
    (ε / s) * lowerAuxiliaryError (s + ε - 1) ≤ upperAuxiliaryError s := by
  have hs0 : 0 < s := by linarith
  have hi := mul_shift_integral_lower_bound 0 s ε lowerAuxiliaryError hs0.le
    (by linarith) hε continuousOn_lowerAuxiliaryError
    (fun t ht => lowerAuxiliaryError_nonneg t ht) antitoneOn_lowerAuxiliaryError
  rw [integral_mul_shift_lowerAuxiliaryError s (s + ε) hs (by linarith)] at hi
  have hn := mul_nonneg (sq_nonneg (s + ε))
    (upperAuxiliaryError_nonneg (s + ε) (by linarith))
  rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
  apply (mul_le_mul_iff_right₀ hs0).mp
  nlinarith

theorem lowerAuxiliaryError_lower_step (s ε : ℝ) (hs : 2 < s) (hε : 0 ≤ ε) :
    (ε / s) * upperAuxiliaryError (s + ε - 1) ≤ lowerAuxiliaryError s := by
  have hs0 : 0 < s := by linarith
  have hi := mul_shift_integral_lower_bound 1 s ε upperAuxiliaryError hs0.le
    (by linarith) hε continuousOn_upperAuxiliaryError
    (fun t ht => upperAuxiliaryError_nonneg t ht) antitoneOn_upperAuxiliaryError
  rw [integral_mul_shift_upperAuxiliaryError s (s + ε) hs.le (by linarith)] at hi
  have hn := mul_nonneg (sq_nonneg (s + ε))
    (lowerAuxiliaryError_nonneg (s + ε) (by linarith))
  rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
  apply (mul_le_mul_iff_right₀ hs0).mp
  nlinarith

end Chen.LinearSieve
