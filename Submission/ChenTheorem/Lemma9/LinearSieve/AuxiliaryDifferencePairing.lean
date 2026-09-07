import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliarySumDecay

set_option autoImplicit true
open Set MeasureTheory

namespace Chen.LinearSieve

noncomputable def auxiliaryErrorDifference (s : ℝ) : ℝ :=
  upperAuxiliaryError s - lowerAuxiliaryError s

theorem continuousOn_auxiliaryErrorDifference :
    ContinuousOn auxiliaryErrorDifference (Ioi 1) :=
  continuousOn_upperAuxiliaryError.sub (continuousOn_lowerAuxiliaryError.mono
    (by intro s hs; change 0 < s; linarith [show 1 < s from hs]))

theorem hasDerivAt_continuousErrorDifference (s : ℝ) (hs : 2 < s) :
    HasDerivAt (fun t => upperContinuousError t - lowerContinuousError t)
      (-auxiliaryErrorDifference s) s := by
  have hu := hasDerivAt_upperContinuousError_all s (by linarith)
  have hl := hasDerivAt_lowerContinuousError s hs
  have h := hu.sub hl
  rw [← hu.deriv, ← hl.deriv] at h
  rw [← neg_neg (deriv upperContinuousError s),
    ← upperAuxiliaryError_eq_neg_deriv s (by linarith),
    ← neg_neg (deriv lowerContinuousError s),
    ← lowerAuxiliaryError_eq_neg_deriv s hs] at h
  exact h.congr_deriv (by dsimp [auxiliaryErrorDifference]; ring)

theorem mul_auxiliaryErrorDifference (s : ℝ) (hs : 3 < s) :
    s * auxiliaryErrorDifference s =
      (upperContinuousError s - lowerContinuousError s) -
        (upperContinuousError (s - 1) - lowerContinuousError (s - 1)) := by
  unfold auxiliaryErrorDifference upperAuxiliaryError lowerAuxiliaryError
  rw [max_eq_left (by linarith), if_neg (by linarith : ¬s ≤ 2)]
  field_simp
  ring

/-- The difference has the opposite-sign, constant-adjoint pairing. -/
theorem auxiliaryErrorDifference_pairing_zero (s : ℝ) (hs : 3 < s) :
    (∫ t in (s - 1)..s, auxiliaryErrorDifference t) =
      -(s * auxiliaryErrorDifference s) := by
  have hab : s - 1 ≤ s := by linarith
  have hd : ∀ t ∈ uIcc (s - 1) s,
      HasDerivAt (fun t => upperContinuousError t - lowerContinuousError t)
        (-auxiliaryErrorDifference t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact hasDerivAt_continuousErrorDifference t (by linarith [ht.1])
  have hc := continuousOn_auxiliaryErrorDifference.mono
    (show Icc (s - 1) s ⊆ Ioi 1 from by
      intro t ht; change 1 < t; linarith [ht.1])
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.neg.intervalIntegrable_of_Icc hab)
  rw [intervalIntegral.integral_neg, ← mul_auxiliaryErrorDifference s hs] at hi
  linarith

/-- The positive adjoint is strictly increasing inside the unit interval,
so the unweighted integral is strictly smaller than the endpoint mass. -/
theorem integral_auxiliaryErrorSum_lt_mass (s : ℝ) (hs : 3 < s) :
    (∫ t in (s - 1)..s, auxiliaryErrorSum t) < s * auxiliaryErrorSum s := by
  have hc := continuousOn_auxiliaryErrorSum.mono
    (show Icc (s - 1) s ⊆ Ioi 1 from by
      intro t ht; change 1 < t; linarith [ht.1])
  have hq : Continuous (fun t : ℝ => auxiliaryAdjoint (t + 1)) := by
    unfold auxiliaryAdjoint
    fun_prop
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show s - 1 < s by linarith) (hc.const_mul (auxiliaryAdjoint s))
    (hq.continuousOn.mul hc)
    (show ∀ t ∈ Ioc (s - 1) s,
      auxiliaryAdjoint s * auxiliaryErrorSum t ≤
        auxiliaryAdjoint (t + 1) * auxiliaryErrorSum t from by
      intro t ht
      exact mul_le_mul_of_nonneg_right
        (monotoneOn_auxiliaryAdjoint (by change 2 ≤ s; linarith)
          (by change 2 ≤ t + 1; linarith [ht.1]) (by linarith [ht.1]))
        (auxiliaryErrorSum_pos t (by linarith [ht.1])).le)
    (show ∃ t ∈ Icc (s - 1) s,
      auxiliaryAdjoint s * auxiliaryErrorSum t <
        auxiliaryAdjoint (t + 1) * auxiliaryErrorSum t from by
      refine ⟨s, ⟨by linarith, le_rfl⟩, ?_⟩
      apply mul_lt_mul_of_pos_right _ (auxiliaryErrorSum_pos s (by linarith))
      dsimp [auxiliaryAdjoint]
      nlinarith)
  simp only [Pi.mul_apply] at hi
  rw [intervalIntegral.integral_const_mul, ← auxiliaryErrorSum_pairing_zero s hs] at hi
  have hp := auxiliaryAdjoint_pos s (by linarith)
  nlinarith

end Chen.LinearSieve
