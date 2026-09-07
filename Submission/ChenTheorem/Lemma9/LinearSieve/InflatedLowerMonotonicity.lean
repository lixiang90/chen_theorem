import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryLowerInitialShift
import Submission.ChenTheorem.Lemma9.LinearSieve.InflationInitialSlope
import Submission.ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryTransport

set_option autoImplicit true
open Filter Set

namespace Chen.LinearSieve

/-- Only interior derivative and shift bounds are needed; continuity supplies
the left endpoint even when the delay equation is not valid there. -/
theorem shiftedInflation_sq_antitone_of_interior_bounds (d D a b B k : ℝ)
    (H J : ℝ → ℝ) (hD : 1 < D) (ha : 0 ≤ a) (hb : 0 < b)
    (hc : ContinuousOn H (Ici b))
    (hd : ∀ s, b < s → HasDerivAt (fun t => t ^ 2 * H t) (-s * J (s - 1)) s)
    (hn : ∀ s, b < s → 0 ≤ H s)
    (hj : ∀ s, b < s → k * s * Real.log s * H s ≤ J (s - 1))
    (hslope : ∀ s, b < s → s < B → auxiliaryInflationSlope d D a s ≤ k * Real.log s) :
    AntitoneOn (fun s => shiftedAuxiliaryInflation d D a s * (s ^ 2 * H s)) (Icc b B) := by
  have hi : ∀ s, b ≤ s → HasDerivAt (shiftedAuxiliaryInflation d D a)
      (shiftedAuxiliaryInflation d D a s * auxiliaryInflationSlope d D a s) s :=
    fun s hs => hasDerivAt_shiftedAuxiliaryInflation d D a s hD (by linarith)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc b B)
    (f' := fun s => shiftedAuxiliaryInflation d D a s * s *
      (auxiliaryInflationSlope d D a s * s * H s - J (s - 1)))
  · have hci : ContinuousOn (shiftedAuxiliaryInflation d D a) (Icc b B) :=
      fun s hs => (hi s hs.1).continuousAt.continuousWithinAt
    exact hci.mul ((continuousOn_id.pow 2).mul (hc.mono (fun _ hs => hs.1)))
  · intro s hs
    rw [interior_Icc] at hs
    apply HasDerivAt.hasDerivWithinAt
    apply ((hi s hs.1.le).mul (hd s hs.1)).congr_deriv
    ring
  · intro s hs
    rw [interior_Icc] at hs
    have hH := hn s hs.1
    have h := mul_le_mul_of_nonneg_right (hslope s hs.1 hs.2)
      (mul_nonneg (show 0 ≤ s by linarith [hs.1]) hH)
    have hj' := hj s hs.1
    have hm : auxiliaryInflationSlope d D a s * s * H s - J (s - 1) ≤ 0 := by nlinarith
    apply mul_nonpos_of_nonneg_of_nonpos _ hm
    apply mul_nonneg _ (by linarith [hs.1])
    unfold shiftedAuxiliaryInflation
    apply Real.rpow_nonneg
    have hp := Real.rpow_nonneg (show 0 ≤ s + a by linarith [hs.1]) d
    have hL := Real.log_pos hD
    positivity

/-- The lower branch decreases all the way from its endpoint two. -/
theorem eventually_inflatedLowerAuxiliary_antitone (d : ℝ) (hd : 0 < d) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      AntitoneOn (fun s => shiftedAuxiliaryInflation d D a s * (s ^ 2 * lowerAuxiliaryError s))
        (Icc 2 (2 * growingSieveParameter d (Real.log D))) := by
  obtain ⟨k, K, hk, _, hshift⟩ := lowerAuxiliaryError_uniform_log_shift
  filter_upwards [eventually_auxiliaryInflationSlope_small_from_two d k hd hk] with D hD
  refine ⟨hD.1, ?_⟩
  intro a ha ha1
  apply shiftedInflation_sq_antitone_of_interior_bounds d D a 2 _ k
    lowerAuxiliaryError upperAuxiliaryError hD.1 ha (by norm_num)
  · exact continuousOn_lowerAuxiliaryError.mono (by intro s hs; change 0 < s; linarith [show 2 ≤ s from hs])
  · exact hasDerivAt_sq_mul_lowerAuxiliaryError
  · exact fun s hs => lowerAuxiliaryError_nonneg s (by linarith)
  · exact fun s hs => (hshift s hs).1
  · exact fun s hs hcut => hD.2 a ha ha1 s hs.le hcut.le

theorem eventually_inflatedLowerAuxiliaryError_transport (d δ : ℝ) (hd : 0 < d) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ s t : ℝ, 2 ≤ s → s ≤ t →
      t ≤ 2 * growingSieveParameter d (Real.log D) →
      inflatedAuxiliaryError d δ D t lowerAuxiliaryError ≤
        (s / t) * inflatedAuxiliaryError d δ D s lowerAuxiliaryError := by
  filter_upwards [eventually_inflatedLowerAuxiliary_antitone d hd] with D hD
  refine ⟨hD.1, ?_⟩
  intro s t hs hst ht
  have h := hD.2 0 (by norm_num) (by norm_num) ⟨hs, hst.trans ht⟩ ⟨hs.trans hst, ht⟩ hst
  simp only [shiftedAuxiliaryInflation, add_zero] at h
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (Real.log_pos hD.1).le (-δ))
  have ht0 : 0 < t := by linarith
  apply (mul_le_mul_iff_left₀ ht0).mp
  unfold inflatedAuxiliaryError auxiliaryInflation auxiliaryErrorScale
  convert! hm using 1 <;> field_simp

end Chen.LinearSieve
