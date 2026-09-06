import ChenTheorem.Lemma9.LinearSieve.ContinuousTerms

open MeasureTheory Set Filter
open scoped Topology

namespace Chen.LinearSieve

/-- Once the integrand vanishes past the upper endpoint, the clamp can
be removed on the active part of the tail. -/
theorem continuousTail_eq_integral_of_zero (c B : ℝ) (h : ℝ → ℝ)
    (hzero : ∀ t, B ≤ t → h t = 0) (s : ℝ) (hs : c ≤ s) :
    continuousTail c B h s = (∫ t in s..B, h t) / s := by
  by_cases hsB : s ≤ B
  · simp [continuousTail, tailCutoff, max_eq_left hs, min_eq_left hsB]
  · rw [continuousTail_eq_zero c B h s (le_of_not_ge hsB)]
    have hI : (∫ t in B..s, h t) = 0 := by
      calc
        _ = ∫ _ in B..s, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le (le_of_not_ge hsB)] at ht
          exact hzero t ht.1
        _ = 0 := by simp
    rw [intervalIntegral.integral_symm B s, hI]
    simp

/-- Differentiation of the compact tail on its active interval. The
vanishing integrand at the support boundary handles that junction too. -/
theorem hasDerivAt_continuousTail (c B : ℝ) (hc : 0 ≤ c) (hcB : c ≤ B)
    (h : ℝ → ℝ) (hh : ContinuousOn h (Ici c)) (hzero : ∀ t, B ≤ t → h t = 0)
    (s : ℝ) (hs : c < s) :
    HasDerivAt (continuousTail c B h) (-(h s + continuousTail c B h s) / s) s := by
  have hs0 : 0 < s := hc.trans_lt hs
  have hi : IntervalIntegrable h volume s B := by
    apply ContinuousOn.intervalIntegrable
    apply hh.mono
    intro t ht
    exact (le_min hs.le hcB).trans ht.1
  have hcont : ContinuousAt h s := (hh s hs.le).continuousAt (Ici_mem_nhds hs)
  have hm : StronglyMeasurableAtFilter h (𝓝 s) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi (hh.mono Ioi_subset_Ici_self) s hs
  have hI := intervalIntegral.integral_hasDerivAt_left hi hm hcont
  have hquot : HasDerivAt (fun x => (∫ t in x..B, h t) / x)
      (-(h s + continuousTail c B h s) / s) s := by
    convert! hI.fun_div (hasDerivAt_id s) hs0.ne' using 1
    dsimp only [id_eq]
    rw [continuousTail_eq_integral_of_zero c B h hzero s hs.le]
    field_simp
    ring
  apply hquot.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with t ht
  exact continuousTail_eq_integral_of_zero c B h hzero t ht.le

theorem hasDerivAt_mul_continuousTail (c B : ℝ) (hc : 0 ≤ c) (hcB : c ≤ B)
    (h : ℝ → ℝ) (hh : ContinuousOn h (Ici c)) (hzero : ∀ t, B ≤ t → h t = 0)
    (s : ℝ) (hs : c < s) :
    HasDerivAt (fun s => s * continuousTail c B h s) (-h s) s := by
  have hs0 : s ≠ 0 := (hc.trans_lt hs).ne'
  convert! (hasDerivAt_id s).mul (hasDerivAt_continuousTail c B hc hcB h hh hzero s hs) using 1
  dsimp only [id_eq]
  field_simp
  ring

end Chen.LinearSieve
