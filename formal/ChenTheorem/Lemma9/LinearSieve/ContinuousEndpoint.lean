import ChenTheorem.Lemma9.LinearSieve.ContinuousPairing

open Set MeasureTheory

namespace Chen.LinearSieve

theorem continuousErrorMass_initial (s : ℝ) (hs : 2 ≤ s) (hs3 : s ≤ 3) :
    continuousErrorMass s = linearSieveInitialConstant + 2 * lowerContinuousError 2 - 2 -
      linearSieveInitialConstant * Real.log (s - 1) := by
  unfold continuousErrorMass
  rw [mul_upperContinuousError_initial s (by linarith) hs3,
    mul_lowerContinuousError_initial s hs (by linarith)]
  ring

theorem continuousErrorMass_pairing_initial :
    2 * continuousErrorMass 3 - (∫ t in (2 : ℝ)..3, continuousErrorMass t) =
      2 * lowerContinuousError 2 - 2 := by
  let A := linearSieveInitialConstant
  let B := 2 * lowerContinuousError 2 - 2
  let f : ℝ → ℝ := fun t => (A + B) * t - A * ((t - 1) * Real.log (t - 1) - (t - 1))
  have hd : ∀ t ∈ uIcc (2 : ℝ) 3, HasDerivAt f (continuousErrorMass t) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] at ht
    have ht0 : t - 1 ≠ 0 := by linarith [ht.1]
    have hsub := (hasDerivAt_id t).sub_const 1
    have hlog := (Real.hasDerivAt_log ht0).comp t hsub
    have h := ((hasDerivAt_id t).const_mul (A + B)).sub
      (((hsub.mul hlog).sub hsub).const_mul A)
    convert! h using 1
    rw [continuousErrorMass_initial t ht.1 ht.2]
    dsimp [A, B]
    field_simp
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (intervalIntegrable_continuousErrorMass 2 3 le_rfl (by norm_num))
  rw [hi, continuousErrorMass_initial 3 (by norm_num) le_rfl]
  norm_num [f, A, B]
  ring

/-- The lower error series attains its sharp endpoint value. This is
deduced from the conserved pairing and decay, with no normalization
assumption on the upper series. -/
theorem lowerContinuousError_two : lowerContinuousError 2 = 1 := by
  have h := continuousErrorMass_pairing_nonneg
  rw [continuousErrorMass_pairing_initial] at h
  have hle := (lowerContinuousError_bounds 2 le_rfl).2
  linarith

theorem continuousErrorMass_pairing_zero (s : ℝ) (hs : 3 ≤ s) :
    (s - 1) * continuousErrorMass s = ∫ t in (s - 1)..s, continuousErrorMass t := by
  have h := continuousErrorMass_pairing s hs
  rw [continuousErrorMass_pairing_initial, lowerContinuousError_two] at h
  linarith

theorem lowerContinuousError_initial (s : ℝ) (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    lowerContinuousError s = 1 - linearSieveInitialConstant * Real.log (s - 1) / s := by
  have h := mul_lowerContinuousError_initial s hs hs4
  rw [lowerContinuousError_two] at h
  have hs0 : s ≠ 0 := by linarith
  field_simp
  nlinarith

end Chen.LinearSieve
