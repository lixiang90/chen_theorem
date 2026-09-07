import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryBarrierUpperCritical
import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryLogarithmicLower

set_option autoImplicit true
open Set Filter

namespace Chen.LinearSieve

theorem upperAuxiliaryBarrier_deriv_pos_of_initial (C A : ℝ)
    (hC : 0 ≤ C) (hA : 4 ≤ A)
    (hinit : ∀ s ∈ Icc A (A + 1), 0 < deriv (auxiliaryBarrierWeight 8 C) s) :
    ∀ s : ℝ, A ≤ s → 0 < deriv (auxiliaryBarrierWeight 8 C) s := by
  intro s hs
  by_contra hn
  have hg := (continuousOn_deriv_auxiliaryBarrierWeight 8 C).neg.mono
    (show Icc A s ⊆ Ioi 3 from by intro t ht; change 3 < t; linarith [ht.1])
  obtain ⟨m, hm, hzero, hbefore⟩ := exists_first_zero_of_nonneg
    (fun t => -deriv (auxiliaryBarrierWeight 8 C) t) A s hs hg
    (neg_neg_of_pos (hinit A ⟨le_rfl, by linarith⟩)) (neg_nonneg.mpr (le_of_not_gt hn))
  have hzero' : deriv (auxiliaryBarrierWeight 8 C) m = 0 := neg_eq_zero.mp hzero
  have hmA : A + 1 < m := by
    by_contra h
    have hz := hinit m ⟨hm.1.le, le_of_not_gt h⟩
    rw [hzero'] at hz
    exact lt_irrefl _ hz
  have hmono : MonotoneOn (auxiliaryBarrierWeight 8 C) (Icc (m - 1) m) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (m - 1) m)
    · intro t ht
      exact (hasDerivAt_auxiliaryBarrierWeight 8 C t
        (by linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hasDerivAt_auxiliaryBarrierWeight 8 C t
        (by linarith [ht.1])).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have h := hbefore t ⟨by linarith [ht.1], ht.2⟩
      linarith
  exact upperAuxiliaryBarrier_no_stationary C m hC (by linarith) hmono hzero'

theorem auxiliaryShiftRatio_logarithmic_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 4 ≤ s →
      auxiliaryShiftRatio s < 8 * Real.log s + C := by
  have hc := continuousOn_auxiliaryShiftRatio.mono
    (show Icc (4 : ℝ) 5 ⊆ Ioi 2 from by intro s hs; change 2 < s; linarith [hs.1])
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (by norm_num : (Icc (4 : ℝ) 5).Nonempty) hc
  let C := auxiliaryShiftRatio m + 1
  have hC : 0 < C := by
    have h := auxiliaryShiftRatio_pos m (by linarith [hm.1])
    dsimp [C]
    linarith
  have hinit : ∀ s ∈ Icc (4 : ℝ) (4 + 1), 0 < deriv (auxiliaryBarrierWeight 8 C) s := by
    intro s hs
    have hs3 : 3 < s := by linarith [hs.1]
    rw [(hasDerivAt_auxiliaryBarrierWeight 8 C s hs3).deriv]
    apply mul_pos (auxiliaryBarrierWeight_pos 8 C s (by linarith))
    have hr := hmax (show s ∈ Icc (4 : ℝ) 5 by constructor <;> linarith [hs.1, hs.2])
    change auxiliaryShiftRatio s ≤ auxiliaryShiftRatio m at hr
    have hl := Real.log_pos (show 1 < s by linarith)
    have hi : 2 / s ≤ (1 / 2 : ℝ) :=
      (div_le_iff₀ (show 0 < s by linarith)).mpr (by linarith [hs.1])
    dsimp [auxiliaryBarrierSlope, C]
    nlinarith
  have hpos := upperAuxiliaryBarrier_deriv_pos_of_initial C 4 hC.le le_rfl hinit
  refine ⟨C + 8, by linarith, ?_⟩
  intro s hs
  have hp := hpos s hs
  rw [(hasDerivAt_auxiliaryBarrierWeight 8 C s (by linarith)).deriv] at hp
  have hw := auxiliaryBarrierWeight_pos 8 C s (by linarith)
  have hf : 0 < auxiliaryBarrierSlope 8 C s - 2 / s - auxiliaryShiftRatio s := by nlinarith
  have hi := div_pos (by norm_num : (0 : ℝ) < 2) (show 0 < s by linarith)
  dsimp [auxiliaryBarrierSlope] at hf
  nlinarith

theorem eventually_auxiliaryShiftRatio_log_upper :
    ∀ᶠ s : ℝ in atTop, auxiliaryShiftRatio s ≤ 9 * Real.log s := by
  obtain ⟨C, _, hC⟩ := auxiliaryShiftRatio_logarithmic_upper_bound
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop C
  filter_upwards [eventually_ge_atTop (4 : ℝ), hlog] with s hs hl
  have h := hC s hs
  linarith

theorem eventually_auxiliaryShiftRatio_log_bounds :
    ∀ᶠ s : ℝ in atTop,
      (1 / 4 : ℝ) * Real.log s ≤ auxiliaryShiftRatio s ∧
      auxiliaryShiftRatio s ≤ 9 * Real.log s :=
  eventually_auxiliaryShiftRatio_log_lower.and eventually_auxiliaryShiftRatio_log_upper

theorem eventually_auxiliaryCrossShift_log_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ s : ℝ in atTop,
      lowerAuxiliaryError (s - 1) / (s * upperAuxiliaryError s) ≤ K * Real.log s ∧
      upperAuxiliaryError (s - 1) / (s * lowerAuxiliaryError s) ≤ K * Real.log s := by
  obtain ⟨c, hc, _, h⟩ := auxiliaryCrossShift_ratios_comparable
  refine ⟨9 / c, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (3 : ℝ), eventually_auxiliaryShiftRatio_log_upper] with s hs hl
  have hb := div_le_div_of_nonneg_right hl hc.le
  have hu := (h s hs).1.2.trans hb
  have hd := (h s hs).2.2.trans hb
  have he : 9 * Real.log s / c = (9 / c) * Real.log s := by ring
  rw [he] at hu hd
  exact ⟨hu, hd⟩

/-- The quantitative cross-shift estimates needed for the inflated sieve
error: both directions have size `s log s`, with fixed positive constants. -/
theorem eventually_auxiliaryCrossShift_log_bounds :
    ∃ k K : ℝ, 0 < k ∧ 0 < K ∧ ∀ᶠ s : ℝ in atTop,
      (k * s * Real.log s * upperAuxiliaryError s ≤ lowerAuxiliaryError (s - 1) ∧
        lowerAuxiliaryError (s - 1) ≤ K * s * Real.log s * upperAuxiliaryError s) ∧
      (k * s * Real.log s * lowerAuxiliaryError s ≤ upperAuxiliaryError (s - 1) ∧
        upperAuxiliaryError (s - 1) ≤ K * s * Real.log s * lowerAuxiliaryError s) := by
  obtain ⟨k, hk, hlo⟩ := eventually_auxiliaryCrossShift_log_lower
  obtain ⟨K, hK, hhi⟩ := eventually_auxiliaryCrossShift_log_upper
  refine ⟨k, K, hk, hK, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ), hlo, hhi] with s hs hl hh
  have hsu := mul_pos (show 0 < s by linarith) (upperAuxiliaryError_pos s (by linarith))
  have hsl := mul_pos (show 0 < s by linarith) (lowerAuxiliaryError_pos s (by linarith))
  have hu1 := (le_div_iff₀ hsu).mp hl.1
  have hu2 := (div_le_iff₀ hsu).mp hh.1
  have hl1 := (le_div_iff₀ hsl).mp hl.2
  have hl2 := (div_le_iff₀ hsl).mp hh.2
  constructor <;> constructor <;> nlinarith

end Chen.LinearSieve
