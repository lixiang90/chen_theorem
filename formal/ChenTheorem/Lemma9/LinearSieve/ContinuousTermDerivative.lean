import ChenTheorem.Lemma9.LinearSieve.ContinuousTailDerivative

open MeasureTheory Set

namespace Chen.LinearSieve

theorem continuousOn_shift_rosserContinuousTerm (n : ℕ) :
    ContinuousOn (fun s => rosserContinuousTerm n (s - 1)) (Ioi 1) := by
  apply (continuousOn_rosserContinuousTerm n).comp (continuousOn_id.sub continuousOn_const)
  intro s hs
  change 0 < s - 1
  exact sub_pos.mpr hs

theorem hasDerivAt_rosserContinuousTerm (n : ℕ) (s : ℝ)
    (hs : rosserContinuousCutoff (n + 2) < s) :
    HasDerivAt (rosserContinuousTerm (n + 2))
      (-(rosserContinuousTerm (n + 1) (s - 1) + rosserContinuousTerm (n + 2) s) / s) s := by
  have hc := rosserContinuousCutoff_bounds (n + 2)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hcont : ContinuousOn (fun t => rosserContinuousTerm (n + 1) (t - 1))
      (Ici (rosserContinuousCutoff (n + 2))) := by
    apply (continuousOn_shift_rosserContinuousTerm (n + 1)).mono
    intro t ht
    change 1 < t
    linarith [show rosserContinuousCutoff (n + 2) ≤ t from ht]
  exact hasDerivAt_continuousTail _ _ (by linarith) (by linarith) _ hcont
    (fun t ht => rosserContinuousTerm_eq_zero (n + 1) (t - 1) (by push_cast; linarith)) s hs

/-- The differential-delay relation satisfied by each individual term
away from its lower cutoff. The upper support junction is included. -/
theorem hasDerivAt_mul_rosserContinuousTerm (n : ℕ) (s : ℝ)
    (hs : rosserContinuousCutoff (n + 2) < s) :
    HasDerivAt (fun s => s * rosserContinuousTerm (n + 2) s)
      (-rosserContinuousTerm (n + 1) (s - 1)) s := by
  have hc := (rosserContinuousCutoff_bounds (n + 2)).1
  have hs0 : s ≠ 0 := by linarith
  convert! (hasDerivAt_id s).mul (hasDerivAt_rosserContinuousTerm n s hs) using 1
  dsimp only [id_eq]
  field_simp
  ring

theorem continuousOn_deriv_rosserContinuousTerm (n : ℕ) :
    ContinuousOn (deriv (rosserContinuousTerm (n + 2)))
      (Ioi (rosserContinuousCutoff (n + 2))) := by
  have hc := (rosserContinuousCutoff_bounds (n + 2)).1
  have hsub1 : Ioi (rosserContinuousCutoff (n + 2)) ⊆ Ioi 1 := by
    intro s hs
    change 1 < s
    linarith [show rosserContinuousCutoff (n + 2) < s from hs]
  have hsub0 : Ioi (rosserContinuousCutoff (n + 2)) ⊆ Ioi 0 := by
    intro s hs
    exact lt_trans zero_lt_one (show 1 < s from hsub1 hs)
  have hcont := (((continuousOn_shift_rosserContinuousTerm (n + 1)).mono hsub1).add
    ((continuousOn_rosserContinuousTerm (n + 2)).mono hsub0)).neg.div continuousOn_id
      (fun s hs => ne_of_gt (hsub0 hs))
  apply hcont.congr
  intro s hs
  exact (hasDerivAt_rosserContinuousTerm n s hs).deriv

theorem deriv_rosserContinuousTerm_nonpos (n : ℕ) (s : ℝ)
    (hs : rosserContinuousCutoff (n + 2) < s) :
    deriv (rosserContinuousTerm (n + 2)) s ≤ 0 := by
  have hc := (rosserContinuousCutoff_bounds (n + 2)).1
  have hs0 : 0 < s := by linarith
  rw [(hasDerivAt_rosserContinuousTerm n s hs).deriv]
  apply div_nonpos_of_nonpos_of_nonneg _ hs0.le
  exact neg_nonpos.mpr (add_nonneg
    (rosserContinuousTerm_nonneg (n + 1) (s - 1) (by linarith))
    (rosserContinuousTerm_nonneg (n + 2) s hs0))

/-- Below the lower cutoff it is `s f_n(s)` that is constant. -/
theorem mul_rosserContinuousTerm_constant_below (n : ℕ) (s : ℝ)
    (hs0 : 0 < s) (hs : s ≤ rosserContinuousCutoff (n + 2)) :
    s * rosserContinuousTerm (n + 2) s = rosserContinuousCutoff (n + 2) *
      rosserContinuousTerm (n + 2) (rosserContinuousCutoff (n + 2)) := by
  have hc := rosserContinuousCutoff_bounds (n + 2)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  change s * continuousTail _ _ _ s = rosserContinuousCutoff (n + 2) * continuousTail _ _ _ _
  rw [mul_continuousTail _ _ _ _ hs0.ne', mul_continuousTail _ _ _ _ (by linarith)]
  simp only [tailCutoff, max_eq_right hs, max_self]

/-- The shifted terms have the weighted monotonicity required by the
parameter-integral comparison. -/
theorem antitoneOn_mul_shift_rosserContinuousTerm (n : ℕ) :
    AntitoneOn (fun s => s * rosserContinuousTerm n (s - 1)) (Ioi 1) := by
  intro s hs t ht hst
  have hs0 : 0 < s - 1 := sub_pos.mpr hs
  have ht0 : 0 < t - 1 := sub_pos.mpr ht
  have hst' : s - 1 ≤ t - 1 := sub_le_sub_right hst 1
  have hw := antitoneOn_mul_rosserContinuousTerm n hs0 ht0 hst'
  have hf := antitoneOn_rosserContinuousTerm n hs0 ht0 hst'
  dsimp only at hw hf ⊢
  nlinarith

end Chen.LinearSieve
