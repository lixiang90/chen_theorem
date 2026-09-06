import ChenTheorem.Lemma9.LinearSieve.InflationSlopeLimit
import ChenTheorem.Lemma9.LinearSieve.AuxiliaryUniformShift

open Filter Set

namespace Chen.LinearSieve

theorem shiftedInflation_sq_auxiliary_antitone (d D a B k : ℝ)
    (H J : ℝ → ℝ) (hD : 1 < D) (ha : 0 ≤ a) (hk : 0 < k)
    (hc : ContinuousOn H (Ici 3))
    (hd : ∀ s, 3 < s → HasDerivAt (fun t => t ^ 2 * H t) (-s * J (s - 1)) s)
    (hn : ∀ s, 3 ≤ s → 0 ≤ H s)
    (hj : ∀ s, 3 ≤ s → k * s * Real.log s * H s ≤ J (s - 1))
    (hslope : ∀ s, 3 ≤ s → s ≤ B → auxiliaryInflationSlope d D a s ≤ (k / 2) * Real.log s) :
    AntitoneOn (fun s => shiftedAuxiliaryInflation d D a s * (s ^ 2 * H s)) (Icc 3 B) := by
  have hi : ∀ s, 3 ≤ s → HasDerivAt (shiftedAuxiliaryInflation d D a)
      (shiftedAuxiliaryInflation d D a s * auxiliaryInflationSlope d D a s) s :=
    fun s hs => hasDerivAt_shiftedAuxiliaryInflation d D a s hD (by linarith)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 3 B)
    (f' := fun s => shiftedAuxiliaryInflation d D a s * s *
      (auxiliaryInflationSlope d D a s * s * H s - J (s - 1)))
  · have hci : ContinuousOn (shiftedAuxiliaryInflation d D a) (Icc 3 B) :=
      fun s hs => (hi s hs.1).continuousAt.continuousWithinAt
    exact hci.mul ((continuousOn_id.pow 2).mul (hc.mono (fun _ hs => hs.1)))
  · intro s hs
    rw [interior_Icc] at hs
    apply HasDerivAt.hasDerivWithinAt
    apply ((hi s hs.1.le).mul (hd s hs.1)).congr_deriv
    ring
  · intro s hs
    rw [interior_Icc] at hs
    have hH := hn s hs.1.le
    have hlog := (Real.log_pos (show 1 < s by linarith [hs.1])).le
    have h := mul_le_mul_of_nonneg_right (hslope s hs.1.le hs.2.le)
      (mul_nonneg (show 0 ≤ s by linarith [hs.1]) hH)
    have hj' := hj s hs.1.le
    have hm : auxiliaryInflationSlope d D a s * s * H s - J (s - 1) ≤ 0 := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hk.le (show 0 ≤ s by linarith [hs.1])) hlog) hH]
    apply mul_nonpos_of_nonneg_of_nonpos _ hm
    apply mul_nonneg _ (by linarith [hs.1])
    unfold shiftedAuxiliaryInflation
    apply Real.rpow_nonneg
    have hp := Real.rpow_nonneg (show 0 ≤ s + a by linarith [hs.1]) d
    have hL := Real.log_pos hD
    positivity

/-- The inflated weighted errors decrease throughout the growing interval,
uniformly for every shift in `[0,1]`. -/
theorem eventually_inflatedAuxiliary_antitone (d : ℝ) (hd : 0 < d) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      AntitoneOn (fun s => shiftedAuxiliaryInflation d D a s * (s ^ 2 * upperAuxiliaryError s))
        (Icc 3 (2 * growingSieveParameter d (Real.log D))) ∧
      AntitoneOn (fun s => shiftedAuxiliaryInflation d D a s * (s ^ 2 * lowerAuxiliaryError s))
        (Icc 3 (2 * growingSieveParameter d (Real.log D))) := by
  obtain ⟨k, K, hk, _, hshift⟩ := auxiliaryCrossShift_uniform_log_bounds
  filter_upwards [eventually_auxiliaryInflationSlope_small d (k / 2) hd (by positivity)] with D hD
  refine ⟨hD.1, ?_⟩
  intro a ha ha1
  constructor
  · apply shiftedInflation_sq_auxiliary_antitone d D a _ k upperAuxiliaryError lowerAuxiliaryError hD.1 ha hk
    · exact continuousOn_upperAuxiliaryError.mono (by intro s hs; change 1 < s; linarith [show 3 ≤ s from hs])
    · exact hasDerivAt_sq_mul_upperAuxiliaryError
    · exact fun s hs => upperAuxiliaryError_nonneg s (by linarith)
    · exact fun s hs => (hshift s hs).1.1
    · exact hD.2 a ha ha1
  · apply shiftedInflation_sq_auxiliary_antitone d D a _ k lowerAuxiliaryError upperAuxiliaryError hD.1 ha hk
    · exact continuousOn_lowerAuxiliaryError.mono (by intro s hs; change 0 < s; linarith [show 3 ≤ s from hs])
    · exact fun s hs => hasDerivAt_sq_mul_lowerAuxiliaryError s (by linarith)
    · exact fun s hs => lowerAuxiliaryError_nonneg s (by linarith)
    · exact fun s hs => (hshift s hs).2.1
    · exact hD.2 a ha ha1

end Chen.LinearSieve
