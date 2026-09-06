import ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryDissipation

open Set MeasureTheory

namespace Chen.LinearSieve

theorem hasDerivAt_auxiliaryInflation (d D t : ℝ) (hD : 1 < D) (ht : 0 < t) :
    HasDerivAt (auxiliaryInflation d D)
      (auxiliaryInflation d D t * auxiliaryInflationSlope d D 0 t) t := by
  have h := hasDerivAt_shiftedAuxiliaryInflation d D 0 t hD (by simpa using ht)
  unfold shiftedAuxiliaryInflation at h
  unfold auxiliaryInflation
  simpa only [add_zero] using h

theorem hasDerivAt_inflatedAuxiliary_weight (d D t : ℝ) (H J : ℝ → ℝ)
    (hD : 1 < D) (ht : 0 < t)
    (hH : HasDerivAt (fun t => t ^ 2 * H t) (-t * J (t - 1)) t) :
    HasDerivAt (fun t => auxiliaryInflation d D t * (t ^ 2 * H t))
      (-inflatedAuxiliaryDissipation d D t H J) t := by
  apply ((hasDerivAt_auxiliaryInflation d D t hD ht).mul hH).congr_deriv
  unfold inflatedAuxiliaryDissipation
  ring

theorem continuousOn_inflatedAuxiliaryDissipation (d D s b : ℝ) (H J : ℝ → ℝ)
    (hD : 1 < D) (hs : 0 < s) (hH : ContinuousOn H (Icc s b))
    (hJ : ContinuousOn (fun t => J (t - 1)) (Icc s b)) :
    ContinuousOn (fun t => inflatedAuxiliaryDissipation d D t H J) (Icc s b) := by
  have hi : ContinuousOn (auxiliaryInflation d D) (Icc s b) :=
    fun t ht => (hasDerivAt_auxiliaryInflation d D t hD (hs.trans_le ht.1)).continuousAt.continuousWithinAt
  have hl : ContinuousOn (auxiliaryInflationSlope d D 0) (Icc s b) :=
    fun t ht => (continuousAt_auxiliaryInflationSlope d D 0 t hD (by linarith [ht.1])).continuousWithinAt
  exact (hi.mul continuousOn_id).mul (hJ.sub ((hl.mul continuousOn_id).mul hH))

/-- Exact integration of the negative parent derivative, requiring its
delay equation only in the interior of the interval. -/
theorem integral_inflatedAuxiliaryDissipation (d D s b : ℝ) (H J : ℝ → ℝ)
    (hD : 1 < D) (hs : 0 < s) (hsb : s ≤ b) (hH : ContinuousOn H (Icc s b))
    (hJ : ContinuousOn (fun t => J (t - 1)) (Icc s b))
    (hd : ∀ t ∈ Ioo s b, HasDerivAt (fun u => u ^ 2 * H u) (-t * J (t - 1)) t) :
    (∫ t in s..b, inflatedAuxiliaryDissipation d D t H J) =
      auxiliaryInflation d D s * (s ^ 2 * H s) - auxiliaryInflation d D b * (b ^ 2 * H b) := by
  have hi : ContinuousOn (auxiliaryInflation d D) (Icc s b) :=
    fun t ht => (hasDerivAt_auxiliaryInflation d D t hD (hs.trans_le ht.1)).continuousAt.continuousWithinAt
  have hc := hi.mul ((continuousOn_id.pow 2).mul hH)
  have hg := continuousOn_inflatedAuxiliaryDissipation d D s b H J hD hs hH hJ
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hsb hc
    (fun t ht => (hasDerivAt_inflatedAuxiliary_weight d D t H J hD (by linarith [ht.1])
      (hd t ht)).hasDerivWithinAt (s := Ioi t))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hsb).mpr (hg.neg.integrableOn_Icc (μ := volume)))
  rw [intervalIntegral.integral_neg] at h
  change -(∫ t in s..b, inflatedAuxiliaryDissipation d D t H J) =
    auxiliaryInflation d D b * (b ^ 2 * H b) - auxiliaryInflation d D s * (s ^ 2 * H s) at h
  linarith

end Chen.LinearSieve
