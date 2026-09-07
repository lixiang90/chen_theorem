import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousTermDerivative

set_option autoImplicit true
open Finset MeasureTheory Set Filter

namespace Chen.LinearSieve

/-- Odd terms through index `2N+1`. -/
noncomputable def upperContinuousPartial (N : ℕ) (s : ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), rosserContinuousTerm (2 * k + 1) s

/-- Even terms through index `2N`. -/
noncomputable def lowerContinuousPartial (N : ℕ) (s : ℝ) : ℝ :=
  ∑ k ∈ range N, rosserContinuousTerm (2 * k + 2) s

theorem upperContinuousPartial_succ (N : ℕ) (s : ℝ) :
    upperContinuousPartial (N + 1) s = upperContinuousPartial N s +
      rosserContinuousTerm (2 * N + 3) s := by
  simp only [upperContinuousPartial, sum_range_succ]
  congr 1

theorem lowerContinuousPartial_succ (N : ℕ) (s : ℝ) :
    lowerContinuousPartial (N + 1) s = lowerContinuousPartial N s +
      rosserContinuousTerm (2 * N + 2) s := sum_range_succ _ _

theorem continuousOn_upperContinuousPartial (N : ℕ) :
    ContinuousOn (upperContinuousPartial N) (Ioi 0) := by
  exact continuousOn_finsetSum _ (fun k _ => continuousOn_rosserContinuousTerm (2 * k + 1))

theorem continuousOn_lowerContinuousPartial (N : ℕ) :
    ContinuousOn (lowerContinuousPartial N) (Ioi 0) := by
  exact continuousOn_finsetSum _ (fun k _ => continuousOn_rosserContinuousTerm (2 * k + 2))

theorem upperContinuousPartial_nonneg (N : ℕ) (s : ℝ) (hs : 0 < s) :
    0 ≤ upperContinuousPartial N s :=
  sum_nonneg (fun k _ => rosserContinuousTerm_nonneg (2 * k + 1) s hs)

theorem lowerContinuousPartial_nonneg (N : ℕ) (s : ℝ) (hs : 0 < s) :
    0 ≤ lowerContinuousPartial N s :=
  sum_nonneg (fun k _ => rosserContinuousTerm_nonneg (2 * k + 2) s hs)

theorem monotone_upperContinuousPartial (s : ℝ) (hs : 0 < s) :
    Monotone (fun N => upperContinuousPartial N s) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [upperContinuousPartial_succ]
  exact le_add_of_nonneg_right (rosserContinuousTerm_nonneg _ s hs)

theorem monotone_lowerContinuousPartial (s : ℝ) (hs : 0 < s) :
    Monotone (fun N => lowerContinuousPartial N s) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [lowerContinuousPartial_succ]
  exact le_add_of_nonneg_right (rosserContinuousTerm_nonneg _ s hs)

theorem antitoneOn_mul_upperContinuousPartial (N : ℕ) :
    AntitoneOn (fun s => s * upperContinuousPartial N s) (Ioi 0) := by
  intro s hs t ht hst
  dsimp [upperContinuousPartial]
  rw [mul_sum, mul_sum]
  exact sum_le_sum (fun k _ => antitoneOn_mul_rosserContinuousTerm (2 * k + 1) hs ht hst)

theorem antitoneOn_mul_lowerContinuousPartial (N : ℕ) :
    AntitoneOn (fun s => s * lowerContinuousPartial N s) (Ioi 0) := by
  intro s hs t ht hst
  dsimp [lowerContinuousPartial]
  rw [mul_sum, mul_sum]
  exact sum_le_sum (fun k _ => antitoneOn_mul_rosserContinuousTerm (2 * k + 2) hs ht hst)

/-- The finite lower sum differentiates to the preceding odd sum.
This statement does not interchange an infinite sum and a derivative. -/
theorem hasDerivAt_mul_lowerContinuousPartial (N : ℕ) (s : ℝ) (hs : 2 < s) :
    HasDerivAt (fun s => s * lowerContinuousPartial (N + 1) s)
      (-upperContinuousPartial N (s - 1)) s := by
  have hd : ∀ k ∈ range (N + 1),
      HasDerivAt (fun s => s * rosserContinuousTerm (2 * k + 2) s)
        (-rosserContinuousTerm (2 * k + 1) (s - 1)) s := by
    intro k _
    apply hasDerivAt_mul_rosserContinuousTerm (2 * k) s
    simpa [rosserContinuousCutoff, Nat.even_add, Nat.even_mul] using hs
  convert! HasDerivAt.sum hd using 1
  · funext x
    simp only [lowerContinuousPartial, mul_sum, Finset.sum_apply]
  · simp [upperContinuousPartial]

/-- The finite odd sum differentiates to the even sum. The first term
vanishes on this open interval, so it contributes zero to the derivative. -/
theorem hasDerivAt_mul_upperContinuousPartial (N : ℕ) (s : ℝ) (hs : 3 < s) :
    HasDerivAt (fun s => s * upperContinuousPartial N s)
      (-lowerContinuousPartial N (s - 1)) s := by
  induction N with
  | zero =>
    have hd : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 s := hasDerivAt_const s 0
    simp only [lowerContinuousPartial, range_zero, sum_empty, neg_zero]
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hs] with t ht
    simp [upperContinuousPartial, rosserContinuousTerm_eq_zero 1 t (by norm_num; linarith)]
  | succ N ih =>
    have hc : rosserContinuousCutoff (2 * N + 1 + 2) < s := by
      simpa [rosserContinuousCutoff, Nat.even_add, Nat.even_mul] using hs
    have hd := hasDerivAt_mul_rosserContinuousTerm (2 * N + 1) s hc
    convert! ih.add hd using 1
    · funext x
      rw [upperContinuousPartial_succ]
      have hn : 2 * N + 1 + 2 = 2 * N + 3 := by omega
      rw [hn]
      dsimp only [Pi.add_apply]
      ring
    · rw [lowerContinuousPartial_succ]
      have hn : 2 * N + 1 + 1 = 2 * N + 2 := by omega
      rw [hn]
      ring

end Chen.LinearSieve
