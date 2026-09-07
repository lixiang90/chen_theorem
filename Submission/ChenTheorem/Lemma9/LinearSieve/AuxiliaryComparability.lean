import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryDifferencePairing

set_option autoImplicit true
open Set MeasureTheory

namespace Chen.LinearSieve

noncomputable def auxiliaryRelativeDifference (s : ℝ) : ℝ :=
  |auxiliaryErrorDifference s| / auxiliaryErrorSum s

theorem continuousOn_auxiliaryRelativeDifference :
    ContinuousOn auxiliaryRelativeDifference (Ioi 1) :=
  continuousOn_auxiliaryErrorDifference.abs.div continuousOn_auxiliaryErrorSum
    (fun s hs => (auxiliaryErrorSum_pos s hs).ne')

theorem auxiliaryRelativeDifference_nonneg (s : ℝ) (hs : 1 < s) :
    0 ≤ auxiliaryRelativeDifference s :=
  div_nonneg (abs_nonneg _) (auxiliaryErrorSum_pos s hs).le

theorem auxiliaryRelativeDifference_lt_one (s : ℝ) (hs : 1 < s) :
    auxiliaryRelativeDifference s < 1 := by
  rw [auxiliaryRelativeDifference, div_lt_one (auxiliaryErrorSum_pos s hs)]
  have hu := upperAuxiliaryError_pos s hs
  have hl := lowerAuxiliaryError_pos s (by linarith)
  dsimp [auxiliaryErrorDifference, auxiliaryErrorSum]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- A local bound for the relative difference extends to the entire half-line
by the two vanishing pairings and a strict integral inequality. -/
theorem auxiliaryRelativeDifference_bound_of_initial (η : ℝ) (hη : 0 ≤ η)
    (hinit : ∀ s ∈ Icc (2 : ℝ) 3, auxiliaryRelativeDifference s ≤ η) :
    ∀ s : ℝ, 2 ≤ s → auxiliaryRelativeDifference s ≤ η := by
  intro s hs
  have hc := continuousOn_auxiliaryRelativeDifference.mono
    (show Icc (2 : ℝ) s ⊆ Ioi 1 from by
      intro t ht; change 1 < t; linarith [ht.1])
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hs) hc
  have hm' : auxiliaryRelativeDifference m ≤ η := by
    by_contra hn
    have hn' : η < auxiliaryRelativeDifference m := lt_of_not_ge hn
    have hMpos : 0 < auxiliaryRelativeDifference m := hη.trans_lt hn'
    have hm3 : 3 < m := by
      by_contra hm3
      exact hn (hinit m ⟨hm.1, le_of_not_gt hm3⟩)
    have hab : m - 1 ≤ m := by linarith
    have hP := continuousOn_auxiliaryErrorDifference.mono
      (show Icc (m - 1) m ⊆ Ioi 1 from by
        intro t ht; change 1 < t; linarith [ht.1])
    have hQ := continuousOn_auxiliaryErrorSum.mono
      (show Icc (m - 1) m ⊆ Ioi 1 from by
        intro t ht; change 1 < t; linarith [ht.1])
    have hi := intervalIntegral.integral_mono_on (μ := volume) hab
      (hP.abs.intervalIntegrable_of_Icc hab)
      ((hQ.const_mul (auxiliaryRelativeDifference m)).intervalIntegrable_of_Icc hab)
      (show ∀ t ∈ Icc (m - 1) m, |auxiliaryErrorDifference t| ≤
        auxiliaryRelativeDifference m * auxiliaryErrorSum t from by
        intro t ht
        have htmax := hmax ⟨by linarith [ht.1], ht.2.trans hm.2⟩
        exact (div_le_iff₀ (auxiliaryErrorSum_pos t (by linarith [ht.1]))).mp htmax)
    have hnorm := intervalIntegral.abs_integral_le_integral_abs
      (f := auxiliaryErrorDifference) (μ := volume) hab
    rw [auxiliaryErrorDifference_pairing_zero m hm3, abs_neg, abs_mul,
      abs_of_pos (show 0 < m by linarith)] at hnorm
    rw [intervalIntegral.integral_const_mul] at hi
    have hstrict := mul_lt_mul_of_pos_left (integral_auxiliaryErrorSum_lt_mass m hm3) hMpos
    have he : auxiliaryRelativeDifference m * auxiliaryErrorSum m =
        |auxiliaryErrorDifference m| :=
      div_mul_cancel₀ _ (auxiliaryErrorSum_pos m (by linarith)).ne'
    nlinarith [congrArg (fun x => m * x) he]
  exact (hmax ⟨hs, le_rfl⟩).trans hm'

theorem auxiliaryRelativeDifference_uniform_bound :
    ∃ η : ℝ, 0 ≤ η ∧ η < 1 ∧
      ∀ s : ℝ, 2 ≤ s → auxiliaryRelativeDifference s ≤ η := by
  have hc := continuousOn_auxiliaryRelativeDifference.mono
    (show Icc (2 : ℝ) 3 ⊆ Ioi 1 from by
      intro t ht; change 1 < t; linarith [ht.1])
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (by norm_num : (Icc (2 : ℝ) 3).Nonempty) hc
  have hm1 : 1 < m := by linarith [hm.1]
  refine ⟨auxiliaryRelativeDifference m, auxiliaryRelativeDifference_nonneg m hm1,
    auxiliaryRelativeDifference_lt_one m hm1, ?_⟩
  exact auxiliaryRelativeDifference_bound_of_initial _
    (auxiliaryRelativeDifference_nonneg m hm1) hmax

/-- Both auxiliary errors are uniformly comparable to their positive sum.
The constant is independent of the sieve level and of the parameter. -/
theorem auxiliaryErrors_comparable_to_sum :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ ∀ s : ℝ, 2 ≤ s →
      (c * auxiliaryErrorSum s ≤ upperAuxiliaryError s ∧
        upperAuxiliaryError s ≤ auxiliaryErrorSum s) ∧
      (c * auxiliaryErrorSum s ≤ lowerAuxiliaryError s ∧
        lowerAuxiliaryError s ≤ auxiliaryErrorSum s) := by
  obtain ⟨η, hη0, hη1, hη⟩ := auxiliaryRelativeDifference_uniform_bound
  refine ⟨(1 - η) / 2, by linarith, by linarith, ?_⟩
  intro s hs
  have h := (div_le_iff₀ (auxiliaryErrorSum_pos s (by linarith))).mp (hη s hs)
  have ha := abs_le.mp h
  have hu := (upperAuxiliaryError_pos s (by linarith)).le
  have hl := (lowerAuxiliaryError_pos s (by linarith)).le
  dsimp [auxiliaryErrorDifference, auxiliaryErrorSum] at ha ⊢
  constructor <;> constructor <;> nlinarith [ha.1, ha.2]

theorem auxiliaryErrors_uniform_comparison :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 2 ≤ s →
      upperAuxiliaryError s ≤ C * lowerAuxiliaryError s ∧
      lowerAuxiliaryError s ≤ C * upperAuxiliaryError s := by
  obtain ⟨c, hc, hc2, h⟩ := auxiliaryErrors_comparable_to_sum
  refine ⟨1 / c, (le_div_iff₀ hc).mpr (by linarith), ?_⟩
  intro s hs
  obtain ⟨hu, hl⟩ := h s hs
  constructor
  · rw [one_div_mul_eq_div, le_div_iff₀ hc]
    nlinarith
  · rw [one_div_mul_eq_div, le_div_iff₀ hc]
    nlinarith

end Chen.LinearSieve
