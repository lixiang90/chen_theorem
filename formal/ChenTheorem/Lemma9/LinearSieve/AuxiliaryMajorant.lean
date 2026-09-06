import ChenTheorem.Lemma9.LinearSieve.AuxiliaryChildSum

open Finset Set

namespace Chen.LinearSieve

theorem upperContinuousError_le_mul_auxiliary (s : ℝ) (hs : 1 < s) :
    upperContinuousError s ≤ s * upperAuxiliaryError s := by
  have hs0 : s ≠ 0 := by linarith
  rw [upperAuxiliaryError, mul_div_cancel₀ _ hs0]
  have h := (lowerContinuousError_bounds _ (le_max_right (s - 1) 2)).1
  linarith

theorem lowerContinuousError_le_mul_auxiliary (s : ℝ) (hs : 2 ≤ s) :
    lowerContinuousError s ≤ s * lowerAuxiliaryError s := by
  rcases eq_or_lt_of_le hs with rfl | hs2
  · rw [lowerContinuousError_two, lowerAuxiliaryError_initial 2 le_rfl]
    norm_num
    linarith [linearSieveInitialConstant_ge_three]
  · have hs0 : s ≠ 0 := by linarith
    rw [lowerAuxiliaryError, if_neg (not_le.mpr hs2), mul_div_cancel₀ _ hs0]
    have h := (upperContinuousError_bounds (s - 1) (by linarith)).1
    linarith

theorem upperContinuousPartial_le_error (N : ℕ) (s : ℝ) (hs : 1 < s) :
    upperContinuousPartial N s ≤ upperContinuousError s := by
  exact (summable_odd_rosserContinuousTerm s hs).sum_le_tsum (range (N + 1))
    (fun k _ => rosserContinuousTerm_nonneg _ s (by linarith))

theorem lowerContinuousPartial_le_error (N : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    lowerContinuousPartial N s ≤ lowerContinuousError s := by
  exact (summable_even_rosserContinuousTerm s hs).sum_le_tsum (range N)
    (fun k _ => rosserContinuousTerm_nonneg _ s (by linarith))

theorem upperContinuousPartial_le_mul_auxiliary (N : ℕ) (s : ℝ) (hs : 1 < s) :
    upperContinuousPartial N s ≤ s * upperAuxiliaryError s :=
  (upperContinuousPartial_le_error N s hs).trans (upperContinuousError_le_mul_auxiliary s hs)

theorem lowerContinuousPartial_le_mul_auxiliary (N : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    lowerContinuousPartial N s ≤ s * lowerAuxiliaryError s :=
  (lowerContinuousPartial_le_error N s hs).trans (lowerContinuousError_le_mul_auxiliary s hs)

end Chen.LinearSieve
