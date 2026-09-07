import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryLogarithmicUpper

set_option autoImplicit true
open Set Filter

namespace Chen.LinearSieve

/-- Compactness fills the finite initial interval in the asymptotic scalar
shift estimates. The resulting constants work for every `s ≥ 3`. -/
theorem auxiliaryShiftRatio_uniform_log_bounds :
    ∃ k K : ℝ, 0 < k ∧ 0 < K ∧ ∀ s : ℝ, 3 ≤ s →
      k * Real.log s ≤ auxiliaryShiftRatio s ∧ auxiliaryShiftRatio s ≤ K * Real.log s := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp eventually_auxiliaryShiftRatio_log_bounds
  let B := max T 3
  let g : ℝ → ℝ := fun s => auxiliaryShiftRatio s / Real.log s
  have hB : 3 ≤ B := le_max_right _ _
  have hR := continuousOn_auxiliaryShiftRatio.mono
    (show Ici (3 : ℝ) ⊆ Ioi 2 from by intro s hs; change 2 < s; linarith [show 3 ≤ s from hs])
  have hL : ContinuousOn Real.log (Ici 3) := by
    intro s hs
    exact (Real.continuousAt_log (by linarith [show 3 ≤ s from hs])).continuousWithinAt
  have hg : ContinuousOn g (Ici 3) := hR.div hL
    (fun s hs => (Real.log_pos (by linarith [show 3 ≤ s from hs] : 1 < s)).ne')
  have hgc := hg.mono (show Icc (3 : ℝ) B ⊆ Ici 3 from fun _ hs => hs.1)
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hB) hgc
  obtain ⟨M, hM, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hB) hgc
  have hgm : 0 < g m := div_pos (auxiliaryShiftRatio_pos m (by linarith [hm.1]))
    (Real.log_pos (by linarith [hm.1]))
  refine ⟨min (1 / 4) (g m), max 9 (g M), lt_min (by norm_num) hgm,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 9) (le_max_left _ _), ?_⟩
  intro s hs
  have hl : 0 < Real.log s := Real.log_pos (by linarith)
  by_cases hsb : s ≤ B
  · have hlow : g m ≤ g s := hmin ⟨hs, hsb⟩
    have hhigh : g s ≤ g M := hmax ⟨hs, hsb⟩
    exact ⟨(le_div_iff₀ hl).mp ((min_le_right _ _).trans hlow),
      (div_le_iff₀ hl).mp (hhigh.trans (le_max_right _ _))⟩
  · have hts : T ≤ s := (le_max_left T 3).trans (le_of_not_ge hsb)
    have h := hT s hts
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hl.le).trans h.1,
      h.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hl.le)⟩

/-- Uniform quantitative shift bounds for both auxiliary errors throughout
the half-line used in the sieve comparison. -/
theorem auxiliaryCrossShift_uniform_log_bounds :
    ∃ k K : ℝ, 0 < k ∧ 0 < K ∧ ∀ s : ℝ, 3 ≤ s →
      (k * s * Real.log s * upperAuxiliaryError s ≤ lowerAuxiliaryError (s - 1) ∧
        lowerAuxiliaryError (s - 1) ≤ K * s * Real.log s * upperAuxiliaryError s) ∧
      (k * s * Real.log s * lowerAuxiliaryError s ≤ upperAuxiliaryError (s - 1) ∧
        upperAuxiliaryError (s - 1) ≤ K * s * Real.log s * lowerAuxiliaryError s) := by
  obtain ⟨k, K, hk, hK, hr⟩ := auxiliaryShiftRatio_uniform_log_bounds
  obtain ⟨c, hc, _, h⟩ := auxiliaryCrossShift_ratios_comparable
  refine ⟨c * k, K / c, mul_pos hc hk, div_pos hK hc, ?_⟩
  intro s hs
  have hlo := mul_le_mul_of_nonneg_left (hr s hs).1 hc.le
  have hhi := div_le_div_of_nonneg_right (hr s hs).2 hc.le
  have he : K * Real.log s / c = (K / c) * Real.log s := by ring
  rw [he] at hhi
  have hu1 := (le_div_iff₀ (mul_pos (show 0 < s by linarith)
    (upperAuxiliaryError_pos s (by linarith)))).mp (hlo.trans (h s hs).1.1)
  have hu2 := (div_le_iff₀ (mul_pos (show 0 < s by linarith)
    (upperAuxiliaryError_pos s (by linarith)))).mp ((h s hs).1.2.trans hhi)
  have hl1 := (le_div_iff₀ (mul_pos (show 0 < s by linarith)
    (lowerAuxiliaryError_pos s (by linarith)))).mp (hlo.trans (h s hs).2.1)
  have hl2 := (div_le_iff₀ (mul_pos (show 0 < s by linarith)
    (lowerAuxiliaryError_pos s (by linarith)))).mp ((h s hs).2.2.trans hhi)
  constructor <;> constructor <;> nlinarith

end Chen.LinearSieve
