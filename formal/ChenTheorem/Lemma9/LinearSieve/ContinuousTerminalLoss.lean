import ChenTheorem.Lemma9.LinearSieve.InflatedTerminalAbsorption

namespace Chen.LinearSieve

theorem rpow_mul_inflatedAuxiliaryError_ge (d δ D t : ℝ) (H : ℝ → ℝ)
    (hD : 1 < D) (ht : 0 ≤ t) (hH : 0 ≤ H t) :
    t * H t ≤ (Real.log D) ^ δ * inflatedAuxiliaryError d δ D t H := by
  have hL := Real.log_pos hD
  have hp : (Real.log D) ^ δ * (Real.log D) ^ (-δ) = 1 := by
    rw [← Real.rpow_add hL]
    simp
  have he : (Real.log D) ^ δ * inflatedAuxiliaryError d δ D t H = auxiliaryInflation d D t * (t * H t) := by
    unfold inflatedAuxiliaryError auxiliaryErrorScale
    calc
      _ = ((Real.log D) ^ δ * (Real.log D) ^ (-δ)) * (auxiliaryInflation d D t * (t * H t)) := by ring
      _ = _ := by rw [hp, one_mul]
  rw [he]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_auxiliaryInflation d D t hD ht) (mul_nonneg ht hH)

/-- The density error from the continuous main terms has one extra
factor `(log D)^δ` relative to the inflated child-error density loss. -/
theorem continuousTerminalLoss_le_parent_factor (d δ D t w K M : ℝ) (H J : ℝ → ℝ)
    (hD : 1 < D) (ht : 1 < t) (hw : 1 < w) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hH : 0 ≤ H t) (hJ : 0 ≤ J (t - 1))
    (hshift : J (t - 1) ≤ M * t * Real.log t * H t) :
    2 * K * ((t - 1) * J (t - 1)) / Real.log w ≤
      ((Real.log D) ^ δ * (2 * K * M * t * Real.log t / Real.log w)) * inflatedAuxiliaryError d δ D t H := by
  have ht0 : 0 ≤ t := by linarith
  have hlog := (Real.log_pos hw).le
  have hc : 0 ≤ 2 * K / Real.log w := by positivity
  have h1 := mul_le_mul_of_nonneg_right (show t - 1 ≤ t by linarith) hJ
  have h2 := mul_le_mul_of_nonneg_left hshift ht0
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hc
  have hf : 0 ≤ 2 * K * M * t * Real.log t / Real.log w := by
    have := (Real.log_pos ht).le
    positivity
  have h4 := mul_le_mul_of_nonneg_left (rpow_mul_inflatedAuxiliaryError_ge d δ D t H hD ht0 hH) hf
  have hbase : 2 * K * ((t - 1) * J (t - 1)) / Real.log w ≤
      (2 * K * M * t * Real.log t / Real.log w) * (t * H t) := by
    convert! h3 using 1 <;> ring
  have h := hbase.trans h4
  convert! h using 1
  ring

end Chen.LinearSieve
