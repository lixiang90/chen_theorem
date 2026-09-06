import ChenTheorem.Lemma9.LinearSieve.ContinuousMass

open Finset MeasureTheory Set

namespace Chen.LinearSieve

/-- The finite mass identity gives a uniform bound before any limiting
argument is made. -/
theorem continuous_mass_partial_identity (N : ℕ) :
    oddContinuousMass N + 2 * lowerContinuousPartial N 2 = 2 := by
  induction N with
  | zero => simp [oddContinuousMass_zero, lowerContinuousPartial]
  | succ N ih =>
    rw [oddContinuousMass_succ, lowerContinuousPartial_succ]
    linarith [evenContinuousMass_balance N]

theorem lowerContinuousPartial_le_one (N : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    lowerContinuousPartial N s ≤ 1 := by
  have h2 : lowerContinuousPartial N 2 ≤ 1 := by
    linarith [continuous_mass_partial_identity N, oddContinuousMass_nonneg N]
  apply le_trans _ h2
  apply sum_le_sum
  intro k _
  exact antitoneOn_rosserContinuousTerm (2 * k + 2) (by norm_num) (by change 0 < s; linarith) hs

theorem summable_even_rosserContinuousTerm (s : ℝ) (hs : 2 ≤ s) :
    Summable (fun N => rosserContinuousTerm (2 * N + 2) s) := by
  apply summable_of_sum_range_le (c := 1)
    (fun N => rosserContinuousTerm_nonneg _ s (by linarith))
  intro N
  exact lowerContinuousPartial_le_one N s hs

/-- Each odd term at `s>1` is controlled by the integral which defines
the following even term at two. -/
theorem oddContinuousTerm_pointwise_bound (N : ℕ) (s : ℝ) (hs : 1 < s) :
    (min s 2 - 1) * rosserContinuousTerm (2 * N + 1) s ≤
      2 * rosserContinuousTerm (2 * N + 2) 2 := by
  let a : ℝ := min s 2
  have ha : 1 < a := lt_min hs (by norm_num)
  have ha2 : a ≤ 2 := min_le_right _ _
  have has : a ≤ s := min_le_left _ _
  have hB : a ≤ (2 * N : ℕ) + 3 := by nlinarith [Nat.cast_nonneg (α := ℝ) (2 * N)]
  have hh : ContinuousOn (rosserContinuousTerm (2 * N + 1))
      (Icc (1 : ℝ) ((2 * N : ℕ) + 3)) :=
    (continuousOn_rosserContinuousTerm _).mono (fun t ht => by change 0 < t; linarith [ht.1])
  have hia : IntervalIntegrable (rosserContinuousTerm (2 * N + 1)) volume 1 a := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ha.le]
    exact hh.mono (Icc_subset_Icc le_rfl hB)
  have hiB : IntervalIntegrable (rosserContinuousTerm (2 * N + 1)) volume 1 ((2 * N : ℕ) + 3) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (ha.le.trans hB)]
    exact hh
  rw [evenContinuousTerm_two_eq_integral]
  calc
    _ = ∫ _ in (1 : ℝ)..a, rosserContinuousTerm (2 * N + 1) s := by simp [a]
    _ ≤ ∫ t in (1 : ℝ)..a, rosserContinuousTerm (2 * N + 1) t := by
      apply intervalIntegral.integral_mono_on ha.le intervalIntegrable_const hia
      intro t ht
      exact antitoneOn_rosserContinuousTerm _ (by change 0 < t; linarith [ht.1])
        (by change 0 < s; linarith) (ht.2.trans has)
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_interval le_rfl ha.le hB _ hiB
      apply ae_restrict_of_forall_mem measurableSet_Ioc
      intro t ht
      exact rosserContinuousTerm_nonneg _ t (by linarith [ht.1])

theorem upperContinuousPartial_le (N : ℕ) (s : ℝ) (hs : 1 < s) :
    upperContinuousPartial N s ≤ 2 / (min s 2 - 1) := by
  have hsum : (min s 2 - 1) * upperContinuousPartial N s ≤
      2 * lowerContinuousPartial (N + 1) 2 := by
    unfold upperContinuousPartial lowerContinuousPartial
    rw [mul_sum, mul_sum]
    exact sum_le_sum (fun k _ => oddContinuousTerm_pointwise_bound k s hs)
  apply (le_div_iff₀ (sub_pos.mpr (lt_min hs (by norm_num)))).mpr
  rw [mul_comm]
  linarith [lowerContinuousPartial_le_one (N + 1) 2 le_rfl]

theorem summable_odd_rosserContinuousTerm (s : ℝ) (hs : 1 < s) :
    Summable (fun N => rosserContinuousTerm (2 * N + 1) s) := by
  apply summable_of_sum_range_le (c := 2 / (min s 2 - 1))
    (fun N => rosserContinuousTerm_nonneg _ s (by linarith))
  intro N
  cases N with
  | zero =>
    simp only [range_zero, sum_empty]
    exact div_nonneg (by norm_num) (sub_pos.mpr (lt_min hs (by norm_num))).le
  | succ N => exact upperContinuousPartial_le N s hs

theorem tsum_even_rosserContinuousTerm_le_one (s : ℝ) (hs : 2 ≤ s) :
    (∑' N, rosserContinuousTerm (2 * N + 2) s) ≤ 1 :=
  (summable_even_rosserContinuousTerm s hs).tsum_le_of_sum_range_le
    (fun N => lowerContinuousPartial_le_one N s hs)

theorem tsum_odd_rosserContinuousTerm_le (s : ℝ) (hs : 1 < s) :
    (∑' N, rosserContinuousTerm (2 * N + 1) s) ≤ 2 / (min s 2 - 1) := by
  apply (summable_odd_rosserContinuousTerm s hs).tsum_le_of_sum_range_le
  intro N
  cases N with
  | zero =>
    simp only [range_zero, sum_empty]
    exact div_nonneg (by norm_num) (sub_pos.mpr (lt_min hs (by norm_num))).le
  | succ N => exact upperContinuousPartial_le N s hs

end Chen.LinearSieve
