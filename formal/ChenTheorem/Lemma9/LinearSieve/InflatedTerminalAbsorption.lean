import ChenTheorem.Lemma9.LinearSieve.InflatedTerminalLoss
import ChenTheorem.Lemma9.LinearSieve.GrowingDensityBudget

open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem terminalFactor_growing_bound (d D t C : ℝ) (hL : 1 < Real.log D)
    (ht : 2 ≤ t) (htB : t ≤ 2 * growingSieveParameter d (Real.log D)) (hC : 0 ≤ C) :
    (C * t * Real.log t / Real.log (growingPrefixCutoff d D)) *
        (2 * growingSieveParameter d (Real.log D)) ≤
      C * (2 * growingSieveParameter d (Real.log D)) ^ 3 *
        Real.log (2 * growingSieveParameter d (Real.log D)) / Real.log D := by
  let B := 2 * growingSieveParameter d (Real.log D)
  have hB : 0 < B := by dsimp [B]; exact mul_pos (by norm_num) (growingSieveParameter_pos d _ hL)
  have hL0 : 0 < Real.log D := by linarith
  have hlog := Real.log_le_log (show 0 < t by linarith) htB
  have hprod := mul_le_mul htB hlog (Real.log_nonneg (show 1 ≤ t by linarith)) hB.le
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hC)
    (div_nonneg (sq_nonneg B) hL0.le)
  rw [log_growingPrefixCutoff]
  change C * t * Real.log t / (Real.log D / B) * B ≤ C * B ^ 3 * Real.log B / Real.log D
  change C * (t * Real.log t) * (B ^ 2 / Real.log D) ≤ C * (B * Real.log B) * (B ^ 2 / Real.log D) at hm
  convert! hm using 1 <;> field_simp

/-- Any prescribed fraction of the `1/B` contraction scale eventually
absorbs the terminal loss, uniformly in the parent parameter. -/
theorem eventually_inflatedTerminalLoss_small_of_shift (d δ K M ε : ℝ)
    (hd : 3 < d) (hδ : δ ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ t : ℝ, ∀ H J : ℝ → ℝ,
      2 ≤ t → t ≤ 2 * growingSieveParameter d (Real.log D) → 0 ≤ H t → 0 ≤ J (t - 1) →
      J (t - 1) ≤ M * t * Real.log t * H t →
      (Real.log D) ^ (-δ) * (2 * K * inflatedChildAuxiliaryWeight d δ D t J /
        Real.log (growingPrefixCutoff d D)) ≤
      (ε / (2 * growingSieveParameter d (Real.log D))) * inflatedAuxiliaryError d δ D t H := by
  have hd0 : 0 < d := by linarith
  have hlim := ((tendsto_growingDensityBudget_zero d 1 ((div_lt_one hd0).mpr hd)).const_mul (2 * K * M)).comp
    Real.tendsto_log_atTop
  simp only [mul_zero] at hlim
  filter_upwards [eventually_growingPrefixCutoff_properties d (by linarith),
    hlim.eventually (gt_mem_nhds hε)] with D hc hbudget
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  simp only [Function.comp_def, Real.rpow_one] at hbudget
  have hbudget' : 2 * K * M * (2 * growingSieveParameter d (Real.log D)) ^ 3 *
      Real.log (2 * growingSieveParameter d (Real.log D)) / Real.log D < ε := by
    convert! hbudget using 1
    ring
  refine ⟨hD, ?_⟩
  intro t H J ht htB hH hJ hshift
  have hB := mul_pos (by norm_num : (0 : ℝ) < 2) (growingSieveParameter_pos d _ hL)
  have hfactor := terminalFactor_growing_bound d D t (2 * K * M) hL ht htB (by positivity)
  have hsmall : 2 * K * M * t * Real.log t / Real.log (growingPrefixCutoff d D) ≤
      ε / (2 * growingSieveParameter d (Real.log D)) := by
    apply (le_div_iff₀ hB).mpr
    exact hfactor.trans hbudget'.le
  have hb := inflatedTerminalLoss_le_parent_factor d δ D t (growingPrefixCutoff d D) K M H J
    hδ hD (by linarith) (by linarith) hK hJ hshift
  exact hb.trans (mul_le_mul_of_nonneg_right hsmall
    (inflatedAuxiliaryError_nonneg d δ D t H hD (by linarith) hH))

theorem eventually_inflatedTerminalLower_small (d δ K ε : ℝ)
    (hd : 3 < d) (hδ : δ ≤ 1) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ t : ℝ, 3 ≤ t → t ≤ 2 * growingSieveParameter d (Real.log D) →
      (Real.log D) ^ (-δ) * (2 * K * inflatedChildAuxiliaryWeight d δ D t lowerAuxiliaryError /
        Real.log (growingPrefixCutoff d D)) ≤
      (ε / (2 * growingSieveParameter d (Real.log D))) * inflatedAuxiliaryError d δ D t upperAuxiliaryError := by
  obtain ⟨k, M, _, hM, hshift⟩ := auxiliaryCrossShift_uniform_log_bounds
  filter_upwards [eventually_inflatedTerminalLoss_small_of_shift d δ K M ε hd hδ hK hM.le hε] with D hD
  intro t ht hcut
  exact hD.2 t upperAuxiliaryError lowerAuxiliaryError (by linarith) hcut
    (upperAuxiliaryError_nonneg _ (by linarith)) (lowerAuxiliaryError_nonneg _ (by linarith)) (hshift t ht).1.2

theorem eventually_inflatedTerminalUpper_small (d δ K ε : ℝ)
    (hd : 3 < d) (hδ : δ ≤ 1) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ t : ℝ, 2 < t → t ≤ 2 * growingSieveParameter d (Real.log D) →
      (Real.log D) ^ (-δ) * (2 * K * inflatedChildAuxiliaryWeight d δ D t upperAuxiliaryError /
        Real.log (growingPrefixCutoff d D)) ≤
      (ε / (2 * growingSieveParameter d (Real.log D))) * inflatedAuxiliaryError d δ D t lowerAuxiliaryError := by
  obtain ⟨k, M, _, hM, hshift⟩ := lowerAuxiliaryError_uniform_log_shift
  filter_upwards [eventually_inflatedTerminalLoss_small_of_shift d δ K M ε hd hδ hK hM.le hε] with D hD
  intro t ht hcut
  exact hD.2 t lowerAuxiliaryError upperAuxiliaryError ht.le hcut
    (lowerAuxiliaryError_nonneg _ (by linarith)) (upperAuxiliaryError_nonneg _ (by linarith)) (hshift t ht).2

end Chen.LinearSieve
