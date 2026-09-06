import ChenTheorem.Lemma9.LinearSieve.ContinuousTail

open MeasureTheory Set

namespace Chen.LinearSieve

/-- Alternating beta-two lower endpoints: two for even terms and three
for odd terms. -/
noncomputable def rosserContinuousCutoff (n : ℕ) : ℝ := if Even n then 2 else 3

theorem rosserContinuousCutoff_bounds (n : ℕ) :
    2 ≤ rosserContinuousCutoff n ∧ rosserContinuousCutoff n ≤ 3 := by
  unfold rosserContinuousCutoff
  split_ifs <;> norm_num

/-- The actual compactly supported terms of the beta-two linear sieve.
The functions are extended to all positive parameters to simplify their
analytic construction; the sieve uses the usual parity-dependent domains. -/
noncomputable def rosserContinuousTerm : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => continuousTail 0 3 (fun _ => 1)
  | n + 2 => continuousTail (rosserContinuousCutoff (n + 2)) ((n : ℝ) + 4)
      (fun t => rosserContinuousTerm (n + 1) (t - 1))

theorem rosserContinuousTerm_one (s : ℝ) (hs : 0 < s) :
    rosserContinuousTerm 1 s = max (3 - s) 0 / s := by
  simp only [rosserContinuousTerm, continuousTail, tailCutoff, max_eq_left hs.le,
    intervalIntegral.integral_const, smul_eq_mul, mul_one]
  congr 1
  by_cases hs3 : s ≤ 3
  · rw [min_eq_left hs3, max_eq_left (by linarith)]
  · rw [min_eq_right (le_of_not_ge hs3), max_eq_right (by linarith)]
    ring

/-- The recurrence produces continuous nonnegative decreasing terms;
their parameter-weighted versions decrease as well. -/
theorem rosserContinuousTerm_properties (n : ℕ) :
    ContinuousOn (rosserContinuousTerm n) (Ioi 0) ∧
      (∀ s ∈ Ioi 0, 0 ≤ rosserContinuousTerm n s) ∧
      AntitoneOn (rosserContinuousTerm n) (Ioi 0) ∧
      AntitoneOn (fun s => s * rosserContinuousTerm n s) (Ioi 0) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    exact ⟨continuousOn_const, fun _ _ => le_rfl, fun _ _ _ _ _ => le_rfl,
      fun _ _ _ _ _ => by simp [rosserContinuousTerm]⟩
  | one =>
    exact ⟨continuousOn_continuousTail 0 3 (by norm_num) _ continuousOn_const,
      fun s hs => continuousTail_nonneg 0 3 (by norm_num) _ (by intro; norm_num) s hs,
      antitoneOn_continuousTail 0 3 (by norm_num) _ continuousOn_const (by intro; norm_num),
      antitoneOn_mul_continuousTail 0 3 (by norm_num) _ continuousOn_const (by intro; norm_num)⟩
  | more n _ ih =>
    have hc := rosserContinuousCutoff_bounds (n + 2)
    have hcB : rosserContinuousCutoff (n + 2) ≤ (n : ℝ) + 4 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hm : MapsTo (fun t : ℝ => t - 1)
        (Icc (rosserContinuousCutoff (n + 2)) ((n : ℝ) + 4)) (Ioi 0) := by
      intro t ht
      change 0 < t - 1
      linarith [ht.1]
    have hcont : ContinuousOn (fun t => rosserContinuousTerm (n + 1) (t - 1))
        (Icc (rosserContinuousCutoff (n + 2)) ((n : ℝ) + 4)) :=
      ih.1.comp (continuousOn_id.sub continuousOn_const) hm
    have hnonneg : ∀ t ∈ Icc (rosserContinuousCutoff (n + 2)) ((n : ℝ) + 4),
        0 ≤ rosserContinuousTerm (n + 1) (t - 1) := fun t ht => ih.2.1 _ (hm ht)
    exact ⟨continuousOn_continuousTail _ _ hcB _ hcont,
      fun s hs => continuousTail_nonneg _ _ hcB _ hnonneg s hs,
      antitoneOn_continuousTail _ _ hcB _ hcont hnonneg,
      antitoneOn_mul_continuousTail _ _ hcB _ hcont hnonneg⟩

theorem continuousOn_rosserContinuousTerm (n : ℕ) :
    ContinuousOn (rosserContinuousTerm n) (Ioi 0) := (rosserContinuousTerm_properties n).1

theorem rosserContinuousTerm_nonneg (n : ℕ) (s : ℝ) (hs : 0 < s) :
    0 ≤ rosserContinuousTerm n s := (rosserContinuousTerm_properties n).2.1 s hs

theorem antitoneOn_rosserContinuousTerm (n : ℕ) :
    AntitoneOn (rosserContinuousTerm n) (Ioi 0) := (rosserContinuousTerm_properties n).2.2.1

theorem antitoneOn_mul_rosserContinuousTerm (n : ℕ) :
    AntitoneOn (fun s => s * rosserContinuousTerm n s) (Ioi 0) :=
  (rosserContinuousTerm_properties n).2.2.2

theorem rosserContinuousTerm_eq_zero (n : ℕ) (s : ℝ) (hs : (n : ℝ) + 2 ≤ s) :
    rosserContinuousTerm n s = 0 := by
  rcases n with _ | (_ | n)
  · rfl
  · exact continuousTail_eq_zero 0 3 _ s (by norm_num at hs ⊢; exact hs)
  · exact continuousTail_eq_zero _ _ _ s (by push_cast at hs; linarith)

end Chen.LinearSieve
