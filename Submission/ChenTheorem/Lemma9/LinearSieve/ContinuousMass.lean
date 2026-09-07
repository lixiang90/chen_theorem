import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousTailMass

set_option autoImplicit true
open MeasureTheory Set

namespace Chen.LinearSieve

noncomputable def oddContinuousMass (N : ℕ) : ℝ :=
  ∫ s in (1 : ℝ)..(2 * N : ℕ) + 3, s * rosserContinuousTerm (2 * N + 1) s

noncomputable def evenContinuousMass (N : ℕ) : ℝ :=
  ∫ s in (2 : ℝ)..(2 * N : ℕ) + 4, s * rosserContinuousTerm (2 * N + 2) s

theorem oddContinuousMass_nonneg (N : ℕ) : 0 ≤ oddContinuousMass N := by
  unfold oddContinuousMass
  apply intervalIntegral.integral_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) (2 * N)])
  intro s hs
  have hs0 : 0 < s := by linarith [hs.1]
  exact mul_nonneg hs0.le (rosserContinuousTerm_nonneg _ s hs0)

theorem evenContinuousMass_nonneg (N : ℕ) : 0 ≤ evenContinuousMass N := by
  unfold evenContinuousMass
  apply intervalIntegral.integral_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) (2 * N)])
  intro s hs
  have hs0 : 0 < s := by linarith [hs.1]
  exact mul_nonneg hs0.le (rosserContinuousTerm_nonneg _ s hs0)

private theorem continuousOn_shift_term_interval (n : ℕ) (c B : ℝ) (hc : 2 ≤ c) :
    ContinuousOn (fun t => rosserContinuousTerm n (t - 1)) (Icc c B) := by
  apply (continuousOn_shift_rosserContinuousTerm n).mono
  intro t ht
  change 1 < t
  linarith [ht.1]

theorem evenContinuousMass_eq_integral (N : ℕ) :
    evenContinuousMass N =
      ∫ t in (1 : ℝ)..(2 * N : ℕ) + 3, (t - 1) * rosserContinuousTerm (2 * N + 1) t := by
  have hc : rosserContinuousCutoff (2 * N + 2) = 2 := by
    simp [rosserContinuousCutoff, Nat.even_add]
  unfold evenContinuousMass
  simp only [rosserContinuousTerm, hc]
  rw [integral_mul_continuousTail 2 2 _ (by norm_num) le_rfl
    (by nlinarith [Nat.cast_nonneg (α := ℝ) (2 * N)]) _
    (continuousOn_shift_term_interval _ _ _ le_rfl)]
  have he : (fun t : ℝ => (t - 2) * rosserContinuousTerm (2 * N + 1) (t - 1)) =
      (fun t => ((t - 1) - 1) * rosserContinuousTerm (2 * N + 1) (t - 1)) := by
    funext t
    congr 1
    ring
  rw [he, intervalIntegral.integral_comp_sub_right (fun t =>
    (t - 1) * rosserContinuousTerm (2 * N + 1) t) 1]
  norm_num
  congr 1
  ring

theorem evenContinuousTerm_two_eq_integral (N : ℕ) :
    2 * rosserContinuousTerm (2 * N + 2) 2 =
      ∫ t in (1 : ℝ)..(2 * N : ℕ) + 3, rosserContinuousTerm (2 * N + 1) t := by
  have hc : rosserContinuousCutoff (2 * N + 2) = 2 := by
    simp [rosserContinuousCutoff, Nat.even_add]
  change 2 * continuousTail _ _ _ 2 = _
  rw [hc, mul_continuousTail _ _ _ _ (by norm_num)]
  have hB : (2 : ℝ) ≤ (2 * N : ℕ) + 4 := by nlinarith [Nat.cast_nonneg (α := ℝ) (2 * N)]
  simp only [tailCutoff, max_self, min_eq_left hB]
  rw [intervalIntegral.integral_comp_sub_right (rosserContinuousTerm (2 * N + 1)) 1]
  norm_num
  congr 1
  ring

/-- Passing from an odd term to the next even term loses exactly twice
the even term's value at the lower endpoint. -/
theorem evenContinuousMass_balance (N : ℕ) :
    evenContinuousMass N + 2 * rosserContinuousTerm (2 * N + 2) 2 = oddContinuousMass N := by
  rw [evenContinuousMass_eq_integral, evenContinuousTerm_two_eq_integral]
  have hh : ContinuousOn (rosserContinuousTerm (2 * N + 1))
      (Icc (1 : ℝ) ((2 * N : ℕ) + 3)) :=
    (continuousOn_rosserContinuousTerm _).mono (fun t ht => by change 0 < t; linarith [ht.1])
  have hB : (1 : ℝ) ≤ (2 * N : ℕ) + 3 := by nlinarith [Nat.cast_nonneg (α := ℝ) (2 * N)]
  have hi : IntervalIntegrable (rosserContinuousTerm (2 * N + 1)) volume 1 ((2 * N : ℕ) + 3) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hB] using hh
  have hiw : IntervalIntegrable (fun t => (t - 1) * rosserContinuousTerm (2 * N + 1) t)
      volume 1 ((2 * N : ℕ) + 3) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hB]
    exact (continuousOn_id.sub continuousOn_const).mul hh
  rw [← intervalIntegral.integral_add hiw hi]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  ring

/-- Passing from an even term to the next odd term preserves this mass. -/
theorem oddContinuousMass_succ (N : ℕ) : oddContinuousMass (N + 1) = evenContinuousMass N := by
  have hn : 2 * (N + 1) + 1 = (2 * N + 1) + 2 := by omega
  have hc : rosserContinuousCutoff ((2 * N + 1) + 2) = 3 := by
    simp [rosserContinuousCutoff, Nat.even_add]
  have hB : ((2 * (N + 1) : ℕ) : ℝ) + 3 = ((2 * N + 1 : ℕ) : ℝ) + 4 := by push_cast; ring
  unfold oddContinuousMass
  rw [hn, hB]
  rw [rosserContinuousTerm, hc]
  rw [integral_mul_continuousTail 1 3 _ (by norm_num) (by norm_num)
    (by nlinarith [Nat.cast_nonneg (α := ℝ) (2 * N + 1)]) _
    (continuousOn_shift_term_interval _ _ _ (by norm_num))]
  rw [intervalIntegral.integral_comp_sub_right (fun t => t * rosserContinuousTerm ((2 * N + 1) + 1) t) 1]
  have hn' : (2 * N + 1) + 1 = 2 * N + 2 := by omega
  rw [hn']
  unfold evenContinuousMass
  congr 1 <;> push_cast <;> ring

theorem oddContinuousMass_zero : oddContinuousMass 0 = 2 := by
  unfold oddContinuousMass
  norm_num only [Nat.mul_zero, Nat.cast_zero, zero_add]
  calc
    _ = ∫ s in (1 : ℝ)..3, (3 - s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hs
      have hs0 : 0 < s := by linarith [hs.1]
      dsimp only
      rw [rosserContinuousTerm_one s hs0, max_eq_left (sub_nonneg.mpr hs.2)]
      field_simp
    _ = 2 := by
      change (∫ s in (1 : ℝ)..3, 3 - id s) = 2
      rw [intervalIntegral.integral_sub intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
      norm_num [integral_id]

end Chen.LinearSieve
