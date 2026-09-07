import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousTermDerivative

set_option autoImplicit true
open MeasureTheory Set Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The source for the left derivative of the parameter-weighted term.
The source is zero on the constant branch, including its right endpoint. -/
noncomputable def rosserTermLeftSource (n : ℕ) (s : ℝ) : ℝ :=
  if rosserContinuousCutoff (n + 2) < s then rosserContinuousTerm (n + 1) (s - 1) else 0

theorem rosserTermLeftSource_nonneg (n : ℕ) (s : ℝ) :
    0 ≤ rosserTermLeftSource n s := by
  unfold rosserTermLeftSource
  split_ifs with hs
  · apply rosserContinuousTerm_nonneg
    linarith [(rosserContinuousCutoff_bounds (n + 2)).1]
  · exact le_rfl

/-- The weighted term has a left derivative at every positive parameter,
including the lower junction where the ordinary derivative can fail. -/
theorem hasDerivWithinAt_mul_rosserContinuousTerm_left (n : ℕ) (s : ℝ) (hs : 0 < s) :
    HasDerivWithinAt (fun t => t * rosserContinuousTerm (n + 2) t)
      (-rosserTermLeftSource n s) (Iio s) s := by
  by_cases hc : rosserContinuousCutoff (n + 2) < s
  · simpa only [rosserTermLeftSource, if_pos hc] using
      (hasDerivAt_mul_rosserContinuousTerm n s hc).hasDerivWithinAt (s := Iio s)
  · have hsc : s ≤ rosserContinuousCutoff (n + 2) := le_of_not_gt hc
    simp only [rosserTermLeftSource, if_neg hc, neg_zero]
    apply (hasDerivWithinAt_const s (Iio s)
      (rosserContinuousCutoff (n + 2) *
        rosserContinuousTerm (n + 2) (rosserContinuousCutoff (n + 2)))).congr_of_eventuallyEq
    · filter_upwards [(eventually_gt_nhds hs).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with t ht0 hts
      exact mul_rosserContinuousTerm_constant_below n t ht0 (hts.le.trans hsc)
    · exact mul_rosserContinuousTerm_constant_below n s hs hsc

theorem hasDerivWithinAt_rosserContinuousTerm_left (n : ℕ) (s : ℝ) (hs : 0 < s) :
    HasDerivWithinAt (rosserContinuousTerm (n + 2))
      (-(rosserTermLeftSource n s + rosserContinuousTerm (n + 2) s) / s) (Iio s) s := by
  have hquot := (hasDerivWithinAt_mul_rosserContinuousTerm_left n s hs).div
    (hasDerivAt_id s).hasDerivWithinAt hs.ne'
  have hderiv : (-rosserTermLeftSource n s * s -
      (s * rosserContinuousTerm (n + 2) s) * 1) / s ^ 2 =
      -(rosserTermLeftSource n s + rosserContinuousTerm (n + 2) s) / s := by
    field_simp
    ring
  dsimp only [id_eq] at hquot
  rw [hderiv] at hquot
  apply hquot.congr_of_eventuallyEq
  · filter_upwards [(eventually_gt_nhds hs).filter_mono nhdsWithin_le_nhds] with t ht
    exact (mul_div_cancel_left₀ _ ht.ne').symm
  · exact (mul_div_cancel_left₀ _ hs.ne').symm

/-- The jump source is integrable on compact intervals. A continuous
clamped extension makes this true even below the domain of the shifted term. -/
theorem integrableOn_rosserTermLeftSource (n : ℕ) (a b : ℝ) :
    IntegrableOn (rosserTermLeftSource n) (Icc a b) := by
  let c := rosserContinuousCutoff (n + 2)
  have hc : 2 ≤ c := (rosserContinuousCutoff_bounds (n + 2)).1
  have hcont : Continuous (fun s => rosserContinuousTerm (n + 1) (max s c - 1)) := by
    apply (continuousOn_rosserContinuousTerm (n + 1)).comp_continuous
      ((continuous_id.max continuous_const).sub continuous_const)
    intro s
    change 0 < max s c - 1
    linarith [le_max_right s c]
  have hi : IntegrableOn ((Ioi c).indicator
      (fun s => rosserContinuousTerm (n + 1) (max s c - 1))) (Icc a b) :=
    hcont.integrableOn_Icc.indicator measurableSet_Ioi
  apply hi.congr_fun _ measurableSet_Icc
  intro s _
  by_cases hs : c < s
  · simp only [indicator_of_mem (show s ∈ Ioi c from hs), max_eq_left hs.le, rosserTermLeftSource,
      show rosserContinuousCutoff (n + 2) < s from hs, if_true]
  · simp only [indicator_of_notMem (show s ∉ Ioi c from hs), rosserTermLeftSource,
      show ¬rosserContinuousCutoff (n + 2) < s from hs, if_false]

theorem integrableOn_rosserTermLeftSource_comp (n : ℕ) (a b : ℝ) (u : ℝ → ℝ)
    (huc : ContinuousOn u (Icc a b)) (hum : Measurable u) :
    IntegrableOn (fun t => rosserTermLeftSource n (u t)) (Icc a b) := by
  let c := rosserContinuousCutoff (n + 2)
  have hc : 2 ≤ c := (rosserContinuousCutoff_bounds (n + 2)).1
  have hcont : ContinuousOn
      (fun t => rosserContinuousTerm (n + 1) (max (u t) c - 1)) (Icc a b) := by
    apply (continuousOn_rosserContinuousTerm (n + 1)).comp
      ((huc.sup continuousOn_const).sub continuousOn_const)
    intro t _
    change 0 < max (u t) c - 1
    linarith [le_max_right (u t) c]
  have hi : IntegrableOn ({t | c < u t}.indicator
      (fun t => rosserContinuousTerm (n + 1) (max (u t) c - 1))) (Icc a b) :=
    hcont.integrableOn_Icc.indicator (measurableSet_lt measurable_const hum)
  apply hi.congr_fun _ measurableSet_Icc
  intro t _
  by_cases ht : c < u t
  · simp only [indicator_of_mem (show t ∈ {t | c < u t} from ht), max_eq_left ht.le, rosserTermLeftSource,
      show rosserContinuousCutoff (n + 2) < u t from ht, if_true]
  · simp only [indicator_of_notMem (show t ∉ {t | c < u t} from ht), rosserTermLeftSource,
      show ¬rosserContinuousCutoff (n + 2) < u t from ht, if_false]

end Chen.LinearSieve
