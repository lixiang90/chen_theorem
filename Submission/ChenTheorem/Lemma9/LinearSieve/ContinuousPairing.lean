import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousInitial

set_option autoImplicit true
open Set MeasureTheory Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The weighted sum of the two convergent sieve errors. -/
noncomputable def continuousErrorMass (s : ℝ) : ℝ :=
  s * upperContinuousError s + s * lowerContinuousError s

theorem continuousOn_continuousErrorMass : ContinuousOn continuousErrorMass (Ici 2) :=
  (continuousOn_id.mul (continuousOn_upperContinuousError_Ici 2 (by norm_num))).add
    (continuousOn_id.mul continuousOn_lowerContinuousError)

theorem continuousErrorMass_nonneg (s : ℝ) (hs : 2 ≤ s) : 0 ≤ continuousErrorMass s := by
  exact add_nonneg
    (mul_nonneg (by linarith) (upperContinuousError_bounds s (by linarith)).1)
    (mul_nonneg (by linarith) (lowerContinuousError_bounds s hs).1)

theorem antitoneOn_continuousErrorMass : AntitoneOn continuousErrorMass (Ici 2) := by
  intro s hs t ht hst
  exact add_le_add
    (antitoneOn_mul_upperContinuousError (by change 1 < s; linarith [show 2 ≤ s from hs])
      (by change 1 < t; linarith [show 2 ≤ t from ht]) hst)
    (antitoneOn_mul_lowerContinuousError hs ht hst)

theorem tendsto_continuousErrorMass_zero : Tendsto continuousErrorMass atTop (𝓝 0) := by
  unfold continuousErrorMass
  simpa only [add_zero] using
    tendsto_mul_upperContinuousError_zero.add tendsto_mul_lowerContinuousError_zero

theorem intervalIntegrable_continuousErrorMass (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable continuousErrorMass volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact continuousOn_continuousErrorMass.mono (fun _ ht => ha.trans ht.1)

theorem hasDerivAt_continuousErrorMass (s : ℝ) (hs : 3 < s) :
    HasDerivAt continuousErrorMass
      (-(upperContinuousError (s - 1) + lowerContinuousError (s - 1))) s := by
  convert! (hasDerivAt_mul_upperContinuousError s hs).add
    (hasDerivAt_mul_lowerContinuousError s (by linarith)) using 1
  ring

theorem hasDerivAt_mul_continuousErrorMass (s : ℝ) (hs : 3 < s) :
    HasDerivAt (fun t => (t - 1) * continuousErrorMass t)
      (continuousErrorMass s - continuousErrorMass (s - 1)) s := by
  convert! ((hasDerivAt_id s).sub_const 1).mul
    (hasDerivAt_continuousErrorMass s hs) using 1
  dsimp [continuousErrorMass]
  ring

/-- The delay equation has a conserved integral pairing. -/
theorem continuousErrorMass_pairing (s : ℝ) (hs : 3 ≤ s) :
    (s - 1) * continuousErrorMass s - (∫ t in (s - 1)..s, continuousErrorMass t) =
      2 * continuousErrorMass 3 - (∫ t in (2 : ℝ)..3, continuousErrorMass t) := by
  have hi23 := intervalIntegrable_continuousErrorMass 2 3 le_rfl (by norm_num)
  have hi3s := intervalIntegrable_continuousErrorMass 3 s (by norm_num) hs
  have hi2m := intervalIntegrable_continuousErrorMass 2 (s - 1) le_rfl (by linarith)
  have hims := intervalIntegrable_continuousErrorMass (s - 1) s (by linarith) (by linarith)
  have hshift : IntervalIntegrable (fun t => continuousErrorMass (t - 1)) volume 3 s := by
    convert! hi2m.comp_sub_right 1 using 1 <;> ring
  have hc : ContinuousOn (fun t => (t - 1) * continuousErrorMass t) (Icc 3 s) :=
    (continuousOn_id.sub continuousOn_const).mul
      (continuousOn_continuousErrorMass.mono (fun t ht => by change 2 ≤ t; linarith [ht.1]))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hc
    (fun t ht => hasDerivAt_mul_continuousErrorMass t ht.1) (hi3s.sub hshift)
  rw [intervalIntegral.integral_sub hi3s hshift,
    intervalIntegral.integral_comp_sub_right] at hftc
  norm_num only [show (3 : ℝ) - 1 = 2 by norm_num] at hftc
  have h1 := intervalIntegral.integral_add_adjacent_intervals hi23 hi3s
  have h2 := intervalIntegral.integral_add_adjacent_intervals hi2m hims
  linarith

theorem continuousErrorMass_pairing_nonneg :
    0 ≤ 2 * continuousErrorMass 3 - (∫ t in (2 : ℝ)..3, continuousErrorMass t) := by
  have hlim : Tendsto (fun s : ℝ => -continuousErrorMass (s - 1)) atTop (𝓝 0) := by
    simpa only [sub_eq_add_neg, neg_zero, Function.comp_apply, id_eq] using (tendsto_continuousErrorMass_zero.comp (tendsto_atTop_add_const_right _ (-1)
      tendsto_id)).neg
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with s hs
  rw [← continuousErrorMass_pairing s hs]
  have hi := intervalIntegrable_continuousErrorMass (s - 1) s (by linarith) (by linarith)
  have hbound := intervalIntegral.integral_mono_on (show s - 1 ≤ s by linarith) hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => continuousErrorMass (s - 1)) volume (s - 1) s)
    (fun t ht => antitoneOn_continuousErrorMass (by change 2 ≤ s - 1; linarith)
      (by change 2 ≤ t; linarith [ht.1]) ht.1)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hbound
  have hn := mul_nonneg (show 0 ≤ s - 1 by linarith) (continuousErrorMass_nonneg s (by linarith))
  nlinarith

end Chen.LinearSieve
