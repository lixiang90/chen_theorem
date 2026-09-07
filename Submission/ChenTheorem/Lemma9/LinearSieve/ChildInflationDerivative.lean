import Submission.ChenTheorem.Lemma9.LinearSieve.InflatedChildWeight

set_option autoImplicit true
open Set

namespace Chen.LinearSieve

theorem continuousAt_auxiliaryInflationSlope (d D a s : ℝ) (hD : 1 < D) (hs : 0 < s + a) :
    ContinuousAt (auxiliaryInflationSlope d D a) s := by
  have hL := Real.log_pos hD
  have hp := Real.rpow_pos_of_pos hs d
  have hb : 0 < 1 + (s + a) ^ d / Real.log D := by positivity
  have hden : 0 < Real.log D + (s + a) ^ d := by positivity
  have hc : ContinuousAt (fun t : ℝ => t + a) s := continuousAt_id.add continuousAt_const
  have hpow := hc.rpow_const (p := d) (Or.inl hs.ne')
  have hpowm := hc.rpow_const (p := d - 1) (Or.inl hs.ne')
  have hnum : ContinuousAt (fun t : ℝ => d * t * (t + a) ^ (d - 1)) s :=
    (continuousAt_const.mul continuousAt_id).mul hpowm
  exact ((continuousAt_const.add (hpow.div_const (Real.log D))).log hb.ne').add
    (hnum.div (continuousAt_const.add hpow) hden.ne')

theorem hasDerivAt_auxiliaryChildInflation (d D s : ℝ) (hD : 1 < D) (hs : 0 < s) :
    HasDerivAt (auxiliaryChildInflation d D)
      (auxiliaryChildInflation d D s * auxiliaryInflationSlope d D 1 (s - 1)) s := by
  have h := (hasDerivAt_shiftedAuxiliaryInflation d D 1 (s - 1) hD (by linarith)).comp s
    ((hasDerivAt_id s).sub_const 1)
  unfold auxiliaryChildInflation
  simpa only [Function.comp_def, shiftedAuxiliaryInflation, auxiliaryChildInflation,
    sub_add_cancel, mul_one, id_eq] using h

theorem continuousOn_auxiliaryChildInflation (d D : ℝ) (hD : 1 < D) :
    ContinuousOn (auxiliaryChildInflation d D) (Ioi 0) :=
  fun s hs => (hasDerivAt_auxiliaryChildInflation d D s hD hs).continuousAt.continuousWithinAt

noncomputable def childInflationPrimeSlope (d D t : ℝ) : ℝ :=
  auxiliaryChildInflation d D (sieveParameter D t) *
    auxiliaryInflationSlope d D 1 (sieveParameter D t - 1) * (-Real.log D * logSieveKernel t)

theorem hasDerivAt_childInflationPrimeWeight (d D t : ℝ) (hD : 1 < D) (ht : 1 < t) :
    HasDerivAt (fun t => auxiliaryChildInflation d D (sieveParameter D t))
      (childInflationPrimeSlope d D t) t :=
  (hasDerivAt_auxiliaryChildInflation d D (sieveParameter D t) hD (sieveParameter_pos hD ht)).comp t
    (hasDerivAt_sieveParameter D t ht)

theorem continuousOn_childInflationPrimeSlope (d D w z : ℝ) (hD : 1 < D) (hw : 2 ≤ w) :
    ContinuousOn (childInflationPrimeSlope d D) (Icc w z) := by
  have hu := continuousOn_sieveParameter D w z hw
  have hi := (continuousOn_auxiliaryChildInflation d D hD).comp hu
    (fun t ht => sieveParameter_pos hD (by linarith [ht.1]))
  have hsl : ContinuousOn (fun t => auxiliaryInflationSlope d D 1 (sieveParameter D t - 1)) (Icc w z) := by
    intro t ht
    have hp := sieveParameter_pos hD (show 1 < t by linarith [ht.1])
    exact (continuousAt_auxiliaryInflationSlope d D 1 (sieveParameter D t - 1) hD (by linarith)).comp_continuousWithinAt
      (f := fun x : ℝ => sieveParameter D x - 1)
      ((hu t ht).sub continuousWithinAt_const)
  exact (hi.mul hsl).mul (continuousOn_const.mul (continuousOn_logSieveKernel w z hw))

end Chen.LinearSieve
