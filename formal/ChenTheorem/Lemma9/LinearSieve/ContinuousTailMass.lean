import ChenTheorem.Lemma9.LinearSieve.ContinuousPartials

open MeasureTheory Set
open scoped Topology

namespace Chen.LinearSieve

/-- The integral of a continuous finite tail, proved by integration by
parts. This is the triangular integration identity needed for the masses. -/
theorem integral_tail_primitive (c B : ℝ) (hcB : c ≤ B) (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc c B)) :
    (∫ s in c..B, ∫ t in s..B, h t) = ∫ t in c..B, (t - c) * h t := by
  have hi : IntegrableOn h (uIcc c B) := by
    rw [uIcc_of_le hcB]
    exact hh.integrableOn_Icc
  have hp := intervalIntegral.continuousOn_primitive_interval_left hi
  have hderiv : ∀ s ∈ Ioo (min c B) (max c B),
      HasDerivAt (fun s => ∫ t in s..B, h t) (-h s) s := by
    intro s hs
    rw [min_eq_left hcB, max_eq_right hcB] at hs
    have hsi : IntervalIntegrable h volume s B := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hs.2.le]
      exact hh.mono (Icc_subset_Icc hs.1.le le_rfl)
    exact intervalIntegral.integral_hasDerivAt_left hsi
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hh.mono Ioo_subset_Icc_self) s hs)
      ((hh s ⟨hs.1.le, hs.2.le⟩).continuousAt (Icc_mem_nhds hs.1 hs.2))
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t : ℝ => t - c) (u' := fun _ => 1)
    (v := fun s => ∫ t in s..B, h t) (v' := fun t => -h t)
    (continuousOn_id.sub continuousOn_const) hp
    (fun t _ => (hasDerivAt_id t).sub_const c) hderiv
    (intervalIntegrable_const) hi.intervalIntegrable.neg
  have he : (∫ t in c..B, (t - c) * -h t) = -(∫ t in c..B, (t - c) * h t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [he] at hparts
  simp only [intervalIntegral.integral_same, mul_zero, sub_self, zero_mul, zero_sub,
    one_mul] at hparts
  linarith

/-- Integrating the parameter-weighted tail from a point below its
cutoff gives a first moment of the integrand. -/
theorem integral_mul_continuousTail (a c B : ℝ) (ha : 0 < a) (hac : a ≤ c)
    (hcB : c ≤ B) (h : ℝ → ℝ) (hh : ContinuousOn h (Icc c B)) :
    (∫ s in a..B, s * continuousTail c B h s) = ∫ t in c..B, (t - a) * h t := by
  have hc : ContinuousOn (fun s => s * continuousTail c B h s) (Icc a B) :=
    continuousOn_id.mul ((continuousOn_continuousTail c B hcB h hh).mono
      (fun s hs => ha.trans_le hs.1))
  have hia : IntervalIntegrable (fun s => s * continuousTail c B h s) volume a c := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hac]
    exact hc.mono (Icc_subset_Icc le_rfl hcB)
  have hic : IntervalIntegrable (fun s => s * continuousTail c B h s) volume c B := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hcB]
    exact hc.mono (Icc_subset_Icc hac le_rfl)
  have hleft : (∫ s in a..c, s * continuousTail c B h s) =
      (c - a) * ∫ t in c..B, h t := by
    calc
      _ = ∫ _ in a..c, (∫ t in c..B, h t) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hac] at hs
        dsimp only
        rw [mul_continuousTail c B h s (ha.trans_le hs.1).ne']
        simp only [tailCutoff, max_eq_right hs.2, min_eq_left hcB]
      _ = _ := by simp
  have hright : (∫ s in c..B, s * continuousTail c B h s) =
      ∫ t in c..B, (t - c) * h t := by
    rw [← integral_tail_primitive c B hcB h hh]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hcB] at hs
    dsimp only
    rw [mul_continuousTail c B h s (ha.trans_le (hac.trans hs.1)).ne']
    simp only [tailCutoff, max_eq_left hs.1, min_eq_left hs.2]
  have hih : IntervalIntegrable h volume c B := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hcB] using hh
  have hiw : IntervalIntegrable (fun t => (t - c) * h t) volume c B := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hcB]
    exact (continuousOn_id.sub continuousOn_const).mul hh
  rw [← intervalIntegral.integral_add_adjacent_intervals hia hic, hleft, hright,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hih.const_mul _) hiw]
  apply intervalIntegral.integral_congr
  intro t _
  ring

end Chen.LinearSieve
