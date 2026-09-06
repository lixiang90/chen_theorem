import ChenTheorem.Lemma9.LinearSieve.AuxiliaryUniformShift

open Set

namespace Chen.LinearSieve

/-- Elementary initial formulas give a positive cross-shift lower bound
on the part of the lower branch not covered by the large-parameter estimate. -/
theorem lowerAuxiliaryError_initial_shift_lower (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3) :
    (1 / 4 : ℝ) * s * lowerAuxiliaryError s ≤ upperAuxiliaryError (s - 1) := by
  have hA := linearSieveInitialConstant_ge_three
  have hH := lowerAuxiliaryError_nonneg s (by linarith)
  have hw := antitoneOn_sq_mul_lowerAuxiliaryError
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (show s ∈ Ioi 0 by change 0 < s; linarith) hs.le
  dsimp only at hw
  rw [sq_mul_lowerAuxiliaryError_initial 2 (by norm_num) le_rfl] at hw
  have hparent : s * lowerAuxiliaryError s ≤ linearSieveInitialConstant := by
    nlinarith [mul_nonneg (show 0 ≤ s * (s - 2) by positivity) hH]
  rw [upperAuxiliaryError_initial (s - 1) (by linarith) (by linarith)]
  have hc : linearSieveInitialConstant / 4 ≤ linearSieveInitialConstant / (s - 1) ^ 2 := by
    apply div_le_div_of_nonneg_left (by linarith) (sq_pos_of_pos (by linarith))
    nlinarith
  linarith

theorem lowerAuxiliaryError_initial_shift_upper (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3) :
    upperAuxiliaryError (s - 1) ≤
      (linearSieveInitialConstant / (2 * lowerAuxiliaryError 3)) * s * lowerAuxiliaryError s := by
  have hA := linearSieveInitialConstant_ge_three
  have hH3 := lowerAuxiliaryError_pos 3 (by norm_num)
  have hanti := antitoneOn_lowerAuxiliaryError
    (show s ∈ Ioi 0 by change 0 < s; linarith) (show (3 : ℝ) ∈ Ioi 0 by norm_num) hs3
  have hparent : 2 * lowerAuxiliaryError 3 ≤ s * lowerAuxiliaryError s := by
    have hH := lowerAuxiliaryError_nonneg s (by linarith)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hparent
    (show 0 ≤ linearSieveInitialConstant / (2 * lowerAuxiliaryError 3) by positivity)
  have he : (linearSieveInitialConstant / (2 * lowerAuxiliaryError 3)) *
      (2 * lowerAuxiliaryError 3) = linearSieveInitialConstant := by field_simp
  rw [he] at hmul
  rw [upperAuxiliaryError_initial (s - 1) (by linarith) (by linarith)]
  have hc : linearSieveInitialConstant / (s - 1) ^ 2 ≤ linearSieveInitialConstant := by
    apply (div_le_iff₀ (sq_pos_of_pos (show 0 < s - 1 by linarith))).mpr
    have hsq : 1 ≤ (s - 1) ^ 2 := by nlinarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq (by linarith : 0 ≤ linearSieveInitialConstant)
  nlinarith

/-- Both logarithmic cross-shift bounds hold on the entire open lower domain. -/
theorem lowerAuxiliaryError_uniform_log_shift :
    ∃ k K : ℝ, 0 < k ∧ 0 < K ∧ ∀ s : ℝ, 2 < s →
      k * s * Real.log s * lowerAuxiliaryError s ≤ upperAuxiliaryError (s - 1) ∧
      upperAuxiliaryError (s - 1) ≤ K * s * Real.log s * lowerAuxiliaryError s := by
  obtain ⟨k, K, hk, hK, hshift⟩ := auxiliaryCrossShift_uniform_log_bounds
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hA := linearSieveInitialConstant_ge_three
  have hH3 := lowerAuxiliaryError_pos 3 (by norm_num)
  let K₀ := linearSieveInitialConstant / (2 * lowerAuxiliaryError 3)
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  refine ⟨min k (1 / (4 * Real.log 3)), max K (K₀ / Real.log 2),
    lt_min hk (by positivity), lt_of_lt_of_le hK (le_max_left _ _), ?_⟩
  intro s hs
  have hH := lowerAuxiliaryError_nonneg s (by linarith)
  have hlog := (Real.log_pos (show 1 < s by linarith)).le
  have hfactor : 0 ≤ s * Real.log s * lowerAuxiliaryError s := by positivity
  by_cases hs3 : 3 ≤ s
  · have h := (hshift s hs3).2
    have hlo := mul_le_mul_of_nonneg_right (min_le_left k (1 / (4 * Real.log 3))) hfactor
    have hhi := mul_le_mul_of_nonneg_right (le_max_left K (K₀ / Real.log 2)) hfactor
    constructor <;> nlinarith [h.1, h.2]
  · have hs3' := le_of_not_ge hs3
    have hl := Real.log_le_log (show 0 < s by linarith) hs3'
    have hl2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hs.le
    have hlo : min k (1 / (4 * Real.log 3)) * Real.log s ≤ 1 / 4 := by
      calc
        _ ≤ (1 / (4 * Real.log 3)) * Real.log s := mul_le_mul_of_nonneg_right (min_le_right _ _) hlog
        _ ≤ (1 / (4 * Real.log 3)) * Real.log 3 := mul_le_mul_of_nonneg_left hl (by positivity)
        _ = _ := by field_simp
    have hhi : K₀ ≤ max K (K₀ / Real.log 2) * Real.log s := by
      calc
        K₀ = (K₀ / Real.log 2) * Real.log 2 := by field_simp
        _ ≤ (K₀ / Real.log 2) * Real.log s := mul_le_mul_of_nonneg_left hl2 (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hlog
    have hmlo := mul_le_mul_of_nonneg_right hlo (mul_nonneg (show 0 ≤ s by linarith) hH)
    have hmhi := mul_le_mul_of_nonneg_right hhi (mul_nonneg (show 0 ≤ s by linarith) hH)
    have h1 := lowerAuxiliaryError_initial_shift_lower s hs hs3'
    have h2 := lowerAuxiliaryError_initial_shift_upper s hs hs3'
    change upperAuxiliaryError (s - 1) ≤ K₀ * s * lowerAuxiliaryError s at h2
    constructor <;> nlinarith

end Chen.LinearSieve
