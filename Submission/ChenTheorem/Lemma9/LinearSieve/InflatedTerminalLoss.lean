import Submission.ChenTheorem.Lemma9.LinearSieve.InflatedContractedChildSum

set_option autoImplicit true
namespace Chen.LinearSieve

theorem inflatedChildWeight_scaled_le_parent (d δ D t M : ℝ) (H J : ℝ → ℝ)
    (hδ : δ ≤ 1) (hD : 1 < D) (ht : 1 < t) (hJ : 0 ≤ J (t - 1))
    (hshift : J (t - 1) ≤ M * t * Real.log t * H t) :
    (Real.log D) ^ (-δ) * inflatedChildAuxiliaryWeight d δ D t J ≤
      (M * t * Real.log t) * inflatedAuxiliaryError d δ D t H := by
  have ht0 : 0 ≤ t := by linarith
  have hI := (auxiliaryInflation_pos d D t hD ht0).le
  have hi := mul_le_mul (auxiliaryChildInflation_le d D t hD ht0)
    (childAuxiliaryWeight_le δ t hδ ht) (childAuxiliaryWeight_nonneg δ t ht) hI
  have hq := mul_le_mul_of_nonneg_right hi hJ
  have hh := mul_le_mul_of_nonneg_left hshift (mul_nonneg hI ht0)
  have h : inflatedChildAuxiliaryWeight d δ D t J ≤
      auxiliaryInflation d D t * t * (M * t * Real.log t * H t) := hq.trans hh
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (Real.log_pos hD).le (-δ))
  unfold inflatedAuxiliaryError auxiliaryErrorScale
  convert! hm using 1
  ring

theorem inflatedTerminalLoss_le_parent_factor (d δ D t w K M : ℝ) (H J : ℝ → ℝ)
    (hδ : δ ≤ 1) (hD : 1 < D) (ht : 1 < t) (hw : 1 < w) (hK : 0 ≤ K)
    (hJ : 0 ≤ J (t - 1)) (hshift : J (t - 1) ≤ M * t * Real.log t * H t) :
    (Real.log D) ^ (-δ) * (2 * K * inflatedChildAuxiliaryWeight d δ D t J / Real.log w) ≤
      (2 * K * M * t * Real.log t / Real.log w) * inflatedAuxiliaryError d δ D t H := by
  have h := inflatedChildWeight_scaled_le_parent d δ D t M H J hδ hD ht hJ hshift
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * K / Real.log w by
    have := Real.log_pos hw
    positivity)
  convert! hm using 1 <;> ring

end Chen.LinearSieve
