import Submission.ChenTheorem.Lemma9.LinearSieve.RosserExactLevel

set_option autoImplicit true
open MeasureTheory Set

namespace Chen.LinearSieve

/-- A lower endpoint clamped to the interval of a compact tail. -/
noncomputable def tailCutoff (c B s : ℝ) : ℝ := min (max s c) B

theorem tailCutoff_mem (c B s : ℝ) (hcB : c ≤ B) : tailCutoff c B s ∈ Icc c B := by
  exact ⟨le_min (le_max_right _ _) hcB, min_le_right _ _⟩

theorem tailCutoff_monotone (c B : ℝ) : Monotone (tailCutoff c B) := by
  intro s t hst
  exact min_le_min (max_le_max hst le_rfl) le_rfl

theorem continuous_tailCutoff (c B : ℝ) : Continuous (tailCutoff c B) :=
  (continuous_id.max continuous_const).min continuous_const

/-- A compact nonnegative tail divided by the positive sieve parameter.
Clamping makes the integral zero past `B` without reversing orientation. -/
noncomputable def continuousTail (c B : ℝ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  (∫ t in tailCutoff c B s..B, h t) / s

theorem continuousTail_eq_zero (c B : ℝ) (h : ℝ → ℝ) (s : ℝ) (hs : B ≤ s) :
    continuousTail c B h s = 0 := by
  have hm : B ≤ max s c := hs.trans (le_max_left _ _)
  simp [continuousTail, tailCutoff, min_eq_right hm]

theorem mul_continuousTail (c B : ℝ) (h : ℝ → ℝ) (s : ℝ) (hs : s ≠ 0) :
    s * continuousTail c B h s = ∫ t in tailCutoff c B s..B, h t := by
  unfold continuousTail
  field_simp

theorem continuousTail_nonneg (c B : ℝ) (hcB : c ≤ B) (h : ℝ → ℝ)
    (hh : ∀ t ∈ Icc c B, 0 ≤ h t) (s : ℝ) (hs : 0 < s) :
    0 ≤ continuousTail c B h s := by
  apply div_nonneg _ hs.le
  apply intervalIntegral.integral_nonneg (tailCutoff_mem c B s hcB).2
  intro t ht
  exact hh t ⟨(tailCutoff_mem c B s hcB).1.trans ht.1, ht.2⟩

theorem continuousOn_continuousTail (c B : ℝ) (hcB : c ≤ B) (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc c B)) : ContinuousOn (continuousTail c B h) (Ioi 0) := by
  have hi : IntegrableOn h (uIcc c B) := by
    rw [uIcc_of_le hcB]
    exact hh.integrableOn_Icc
  have hp := intervalIntegral.continuousOn_primitive_interval_left hi
  rw [uIcc_of_le hcB] at hp
  have hcomp : ContinuousOn (fun s => ∫ t in tailCutoff c B s..B, h t) (Ioi 0) :=
    hp.comp (continuous_tailCutoff c B).continuousOn (fun s _ => tailCutoff_mem c B s hcB)
  exact hcomp.div continuousOn_id (fun s hs => ne_of_gt hs)

theorem antitoneOn_mul_continuousTail (c B : ℝ) (hcB : c ≤ B) (h : ℝ → ℝ)
    (hhc : ContinuousOn h (Icc c B)) (hh : ∀ t ∈ Icc c B, 0 ≤ h t) :
    AntitoneOn (fun s => s * continuousTail c B h s) (Ioi 0) := by
  intro s hs t ht hst
  dsimp only
  rw [mul_continuousTail c B h s (ne_of_gt hs), mul_continuousTail c B h t (ne_of_gt ht)]
  have hsi := tailCutoff_mem c B s hcB
  have hti := tailCutoff_mem c B t hcB
  have hic : ContinuousOn h (Icc (tailCutoff c B s) B) :=
    hhc.mono (Icc_subset_Icc hsi.1 le_rfl)
  have hi : IntervalIntegrable h volume (tailCutoff c B s) B := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hsi.2] using hic
  apply intervalIntegral.integral_mono_interval (tailCutoff_monotone c B hst) hti.2 le_rfl _ hi
  apply ae_restrict_of_forall_mem measurableSet_Ioc
  intro x hx
  exact hh x ⟨hsi.1.trans hx.1.le, hx.2⟩

theorem antitoneOn_continuousTail (c B : ℝ) (hcB : c ≤ B) (h : ℝ → ℝ)
    (hhc : ContinuousOn h (Icc c B)) (hh : ∀ t ∈ Icc c B, 0 ≤ h t) :
    AntitoneOn (continuousTail c B h) (Ioi 0) := by
  intro s hs t ht hst
  have hmul := antitoneOn_mul_continuousTail c B hcB h hhc hh hs ht hst
  have hn := continuousTail_nonneg c B hcB h hh s hs
  have hsn : 0 < s := hs
  nlinarith

end Chen.LinearSieve
