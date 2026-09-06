import ChenTheorem.Lemma9.LinearSieve.ContinuousTerminalLoss

open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem eventually_growingTerminalFactor_small (d δ C ε : ℝ) (hd : 3 < d)
    (hgap : 3 / d < 1 - δ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ 1 < growingPrefixCutoff d D ∧ ∀ t : ℝ,
      2 ≤ t → t ≤ 2 * growingSieveParameter d (Real.log D) →
      (Real.log D) ^ δ * (C * t * Real.log t / Real.log (growingPrefixCutoff d D)) ≤
        ε / (2 * growingSieveParameter d (Real.log D)) := by
  have hlim := ((tendsto_growingDensityBudget_zero d (1 - δ) hgap).const_mul C).comp Real.tendsto_log_atTop
  simp only [mul_zero] at hlim
  filter_upwards [eventually_growingPrefixCutoff_properties d (by linarith),
    hlim.eventually (gt_mem_nhds hε)] with D hc hbudget
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  dsimp only [Function.comp_def] at hbudget
  have hL0 : 0 < Real.log D := by linarith
  have hp := Real.rpow_pos_of_pos hL0 δ
  have hbudget' : C * (2 * growingSieveParameter d (Real.log D)) ^ 3 *
      Real.log (2 * growingSieveParameter d (Real.log D)) / (Real.log D) ^ (1 - δ) < ε := by
    convert! hbudget using 1
    ring
  refine ⟨hD, by linarith, ?_⟩
  intro t ht htB
  have hB := mul_pos (by norm_num : (0 : ℝ) < 2) (growingSieveParameter_pos d _ hL)
  have hf := terminalFactor_growing_bound d D t C hL ht htB hC
  have hm := mul_le_mul_of_nonneg_left hf hp.le
  have he : (Real.log D) ^ δ * (C * (2 * growingSieveParameter d (Real.log D)) ^ 3 *
        Real.log (2 * growingSieveParameter d (Real.log D)) / Real.log D) =
      C * (2 * growingSieveParameter d (Real.log D)) ^ 3 *
        Real.log (2 * growingSieveParameter d (Real.log D)) / (Real.log D) ^ (1 - δ) := by
    rw [Real.rpow_sub hL0, Real.rpow_one]
    field_simp
  rw [he] at hm
  apply (le_div_iff₀ hB).mpr
  have h := hm.trans hbudget'.le
  convert! h using 1
  ring

theorem eventually_continuousTerminalLoss_small_of_shift (d δ K M ε : ℝ)
    (hd : 3 < d) (hgap : 3 / d < 1 - δ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ t : ℝ, ∀ H J : ℝ → ℝ,
      2 ≤ t → t ≤ 2 * growingSieveParameter d (Real.log D) → 0 ≤ H t → 0 ≤ J (t - 1) →
      J (t - 1) ≤ M * t * Real.log t * H t →
      2 * K * ((t - 1) * J (t - 1)) / Real.log (growingPrefixCutoff d D) ≤
        (ε / (2 * growingSieveParameter d (Real.log D))) * inflatedAuxiliaryError d δ D t H := by
  filter_upwards [eventually_growingTerminalFactor_small d δ (2 * K * M) ε hd hgap (by positivity) hε] with D hD
  intro t H J ht htB hH hJ hshift
  have h := continuousTerminalLoss_le_parent_factor d δ D t (growingPrefixCutoff d D) K M H J
    hD.1 (by linarith) hD.2.1 hK hM hH hJ hshift
  exact h.trans (mul_le_mul_of_nonneg_right (hD.2.2 t ht htB)
    (inflatedAuxiliaryError_nonneg d δ D t H hD.1 (by linarith) hH))

theorem eventually_continuousTerminalLower_small (d δ K ε : ℝ)
    (hd : 3 < d) (hgap : 3 / d < 1 - δ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ t : ℝ, 3 ≤ t → t ≤ 2 * growingSieveParameter d (Real.log D) →
      2 * K * ((t - 1) * lowerAuxiliaryError (t - 1)) / Real.log (growingPrefixCutoff d D) ≤
        (ε / (2 * growingSieveParameter d (Real.log D))) * inflatedAuxiliaryError d δ D t upperAuxiliaryError := by
  obtain ⟨k, M, _, hM, hshift⟩ := auxiliaryCrossShift_uniform_log_bounds
  filter_upwards [eventually_continuousTerminalLoss_small_of_shift d δ K M ε hd hgap hK hM.le hε] with D hD
  intro t ht hcut
  exact hD t upperAuxiliaryError lowerAuxiliaryError (by linarith) hcut
    (upperAuxiliaryError_nonneg _ (by linarith)) (lowerAuxiliaryError_nonneg _ (by linarith)) (hshift t ht).1.2

theorem eventually_continuousTerminalUpper_small (d δ K ε : ℝ)
    (hd : 3 < d) (hgap : 3 / d < 1 - δ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ t : ℝ, 2 < t → t ≤ 2 * growingSieveParameter d (Real.log D) →
      2 * K * ((t - 1) * upperAuxiliaryError (t - 1)) / Real.log (growingPrefixCutoff d D) ≤
        (ε / (2 * growingSieveParameter d (Real.log D))) * inflatedAuxiliaryError d δ D t lowerAuxiliaryError := by
  obtain ⟨k, M, _, hM, hshift⟩ := lowerAuxiliaryError_uniform_log_shift
  filter_upwards [eventually_continuousTerminalLoss_small_of_shift d δ K M ε hd hgap hK hM.le hε] with D hD
  intro t ht hcut
  exact hD t lowerAuxiliaryError upperAuxiliaryError ht.le hcut
    (lowerAuxiliaryError_nonneg _ (by linarith)) (upperAuxiliaryError_nonneg _ (by linarith)) (hshift t ht).2

end Chen.LinearSieve
