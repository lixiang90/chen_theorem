import ChenTheorem.Lemma9.LinearSieve.AuxiliaryComparability

namespace Chen.LinearSieve

/-- The logarithmic decay rate of the scalar auxiliary equation, apart
from its elementary `2/s` term. -/
noncomputable def auxiliaryShiftRatio (s : ℝ) : ℝ :=
  auxiliaryErrorSum (s - 1) / (s * auxiliaryErrorSum s)

theorem auxiliaryShiftRatio_pos (s : ℝ) (hs : 2 < s) :
    0 < auxiliaryShiftRatio s :=
  div_pos (auxiliaryErrorSum_pos _ (by linarith))
    (mul_pos (by linarith) (auxiliaryErrorSum_pos _ (by linarith)))

theorem normalized_shift_ratio_bounds (c s Q R H J : ℝ)
    (hc : 0 < c) (hs : 0 < s) (hQ : 0 < Q) (hR : 0 < R)
    (hH : c * Q ≤ H ∧ H ≤ Q) (hJ : c * R ≤ J ∧ J ≤ R) :
    c * (R / (s * Q)) ≤ J / (s * H) ∧
      J / (s * H) ≤ (R / (s * Q)) / c := by
  have hHp := (mul_pos hc hQ).trans_le hH.1
  have hJp := (mul_pos hc hR).trans_le hJ.1
  constructor
  · calc
      c * (R / (s * Q)) = (c * R) / (s * Q) := by ring
      _ ≤ J / (s * Q) := div_le_div_of_nonneg_right hJ.1 (mul_pos hs hQ).le
      _ ≤ J / (s * H) := div_le_div_of_nonneg_left hJp.le
        (mul_pos hs hHp) (mul_le_mul_of_nonneg_left hH.2 hs.le)
  · calc
      J / (s * H) ≤ R / (s * H) :=
        div_le_div_of_nonneg_right hJ.2 (mul_pos hs hHp).le
      _ ≤ R / (s * (c * Q)) := div_le_div_of_nonneg_left hR.le
        (mul_pos hs (mul_pos hc hQ)) (mul_le_mul_of_nonneg_left hH.1 hs.le)
      _ = (R / (s * Q)) / c := by ring

/-- The two cross-shift ratios have the same size as the scalar shift ratio,
with constants uniform on the entire analytic half-line. -/
theorem auxiliaryCrossShift_ratios_comparable :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ ∀ s : ℝ, 3 ≤ s →
      (c * auxiliaryShiftRatio s ≤
          lowerAuxiliaryError (s - 1) / (s * upperAuxiliaryError s) ∧
        lowerAuxiliaryError (s - 1) / (s * upperAuxiliaryError s) ≤
          auxiliaryShiftRatio s / c) ∧
      (c * auxiliaryShiftRatio s ≤
          upperAuxiliaryError (s - 1) / (s * lowerAuxiliaryError s) ∧
        upperAuxiliaryError (s - 1) / (s * lowerAuxiliaryError s) ≤
          auxiliaryShiftRatio s / c) := by
  obtain ⟨c, hc, hc2, h⟩ := auxiliaryErrors_comparable_to_sum
  refine ⟨c, hc, hc2, ?_⟩
  intro s hs
  have hp := h s (by linarith)
  have ht := h (s - 1) (by linarith)
  constructor
  · exact normalized_shift_ratio_bounds c s _ _ _ _ hc (by linarith)
      (auxiliaryErrorSum_pos s (by linarith))
      (auxiliaryErrorSum_pos (s - 1) (by linarith)) hp.1 ht.2
  · exact normalized_shift_ratio_bounds c s _ _ _ _ hc (by linarith)
      (auxiliaryErrorSum_pos s (by linarith))
      (auxiliaryErrorSum_pos (s - 1) (by linarith)) hp.2 ht.1

theorem auxiliaryShiftRatio_lower (s : ℝ) (hs : 3 < s) :
    (1 / 3 : ℝ) ≤ auxiliaryShiftRatio s := by
  rw [auxiliaryShiftRatio, le_div_iff₀
    (mul_pos (show 0 < s by linarith) (auxiliaryErrorSum_pos s (by linarith)))]
  linarith [auxiliaryErrorSum_shift_lower s hs]

/-- A first uniform cross-shift estimate, sufficient to control inflation
where its logarithmic derivative tends uniformly to zero. -/
theorem auxiliaryCrossShift_uniform_lower :
    ∃ k : ℝ, 0 < k ∧ ∀ s : ℝ, 3 < s →
      k * s * upperAuxiliaryError s ≤ lowerAuxiliaryError (s - 1) ∧
      k * s * lowerAuxiliaryError s ≤ upperAuxiliaryError (s - 1) := by
  obtain ⟨c, hc, _, h⟩ := auxiliaryCrossShift_ratios_comparable
  refine ⟨c / 3, by positivity, ?_⟩
  intro s hs
  have hb := mul_le_mul_of_nonneg_left (auxiliaryShiftRatio_lower s hs) hc.le
  have he : c * (1 / 3 : ℝ) = c / 3 := by ring
  rw [he] at hb
  have hu := (le_div_iff₀ (mul_pos (show 0 < s by linarith)
    (upperAuxiliaryError_pos s (by linarith)))).mp (hb.trans (h s hs.le).1.1)
  have hl := (le_div_iff₀ (mul_pos (show 0 < s by linarith)
    (lowerAuxiliaryError_pos s (by linarith)))).mp (hb.trans (h s hs.le).2.1)
  constructor <;> nlinarith

end Chen.LinearSieve
