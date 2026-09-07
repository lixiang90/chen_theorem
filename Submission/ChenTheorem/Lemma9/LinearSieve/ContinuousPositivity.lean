import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousAuxiliary

set_option autoImplicit true
open Set

namespace Chen.LinearSieve

/-- Every positive-depth term is strictly positive in the interior of its support. -/
theorem rosserContinuousTerm_pos (n : ℕ) (s : ℝ) (hs : 0 < s)
    (hstop : s < (n : ℝ) + 3) :
    0 < rosserContinuousTerm (n + 1) s := by
  induction n generalizing s with
  | zero =>
    rw [rosserContinuousTerm_one s hs, max_eq_left (by norm_num at hstop; linarith)]
    exact div_pos (by norm_num at hstop; linarith) hs
  | succ n ih =>
    have hc := rosserContinuousCutoff_bounds (n + 2)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hsB : s < (n : ℝ) + 4 := by push_cast at hstop; linarith
    have haB : max s (rosserContinuousCutoff (n + 2)) < (n : ℝ) + 4 :=
      max_lt hsB (by linarith)
    have ha2 : 2 ≤ max s (rosserContinuousCutoff (n + 2)) :=
      hc.1.trans (le_max_right _ _)
    change 0 < continuousTail (rosserContinuousCutoff (n + 2)) ((n : ℝ) + 4)
      (fun t => rosserContinuousTerm (n + 1) (t - 1)) s
    rw [continuousTail, tailCutoff, min_eq_left haB.le]
    apply div_pos _ hs
    apply intervalIntegral.integral_pos haB
    · exact (continuousOn_rosserContinuousTerm (n + 1)).comp
        (continuousOn_id.sub continuousOn_const)
        (fun t ht => by change 0 < t - 1; linarith [ht.1])
    · intro t ht
      exact rosserContinuousTerm_nonneg _ _ (by linarith [ht.1])
    · refine ⟨max s (rosserContinuousCutoff (n + 2)), ⟨le_rfl, haB.le⟩, ?_⟩
      exact ih _ (by linarith) (by linarith)

theorem upperContinuousError_pos (s : ℝ) (hs : 1 < s) :
    0 < upperContinuousError s := by
  obtain ⟨n, hn⟩ := exists_nat_gt s
  have hp := rosserContinuousTerm_pos (2 * n) s (by linarith)
    (by push_cast; have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hsum := (summable_odd_rosserContinuousTerm s hs).sum_le_tsum {n}
    (fun k _ => rosserContinuousTerm_nonneg _ s (by linarith))
  simp only [Finset.sum_singleton] at hsum
  exact hp.trans_le hsum

theorem lowerContinuousError_pos (s : ℝ) (hs : 2 ≤ s) :
    0 < lowerContinuousError s := by
  obtain ⟨n, hn⟩ := exists_nat_gt s
  have hp := rosserContinuousTerm_pos (2 * n + 1) s (by linarith)
    (by push_cast; have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hsum := (summable_even_rosserContinuousTerm s hs).sum_le_tsum {n}
    (fun k _ => rosserContinuousTerm_nonneg _ s (by linarith))
  simp only [Finset.sum_singleton] at hsum
  exact hp.trans_le hsum

theorem upperAuxiliaryError_pos (s : ℝ) (hs : 1 < s) :
    0 < upperAuxiliaryError s := by
  apply div_pos _ (by linarith : 0 < s)
  exact add_pos_of_nonneg_of_pos
    (lowerContinuousError_bounds _ (le_max_right _ _)).1 (upperContinuousError_pos s hs)

theorem lowerAuxiliaryError_pos (s : ℝ) (hs : 0 < s) :
    0 < lowerAuxiliaryError s := by
  rw [lowerAuxiliaryError]
  split_ifs with hs2
  · have hA : 0 < linearSieveInitialConstant := by
      linarith [linearSieveInitialConstant_ge_three]
    positivity
  · apply div_pos _ hs
    exact add_pos_of_pos_of_nonneg (upperContinuousError_pos _ (by linarith))
      (lowerContinuousError_bounds s (by linarith)).1

end Chen.LinearSieve
