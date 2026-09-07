import Submission.ChenTheorem.Lemma9.LinearSieve.RosserPartialDefect
import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousEndpoint

set_option autoImplicit true
namespace Chen.LinearSieve

/-- The same convergent lower error series controls the stopped range.
Its value below two is determined by the constant weighted summands. -/
theorem lowerContinuousError_below_two (s : ℝ) (hs : 0 < s) (hs2 : s ≤ 2) :
    lowerContinuousError s = 2 / s := by
  have he : s * lowerContinuousError s = 2 * lowerContinuousError 2 := by
    simp only [lowerContinuousError, ← tsum_mul_left]
    apply tsum_congr
    intro N
    have hc : rosserContinuousCutoff (2 * N + 2) = 2 := by
      simp [rosserContinuousCutoff, Nat.even_add]
    have h := mul_rosserContinuousTerm_constant_below (2 * N) s hs (by rwa [hc])
    simpa only [hc] using h
  rw [lowerContinuousError_two, mul_one] at he
  apply (eq_div_iff hs.ne').mpr
  nlinarith

theorem one_le_lowerContinuousError_of_le_two (s : ℝ) (hs : 0 < s) (hs2 : s ≤ 2) :
    1 ≤ lowerContinuousError s := by
  rw [lowerContinuousError_below_two s hs hs2]
  exact (le_div_iff₀ hs).mpr (by simpa using hs2)

theorem sieveParameter_le_two_of_stop {D z : ℝ} (hD : 1 < D) (hz : 1 < z)
    (hstop : D ≤ z ^ 2) : sieveParameter D z ≤ 2 := by
  apply (div_le_iff₀ (Real.log_pos hz)).mpr
  have h := Real.log_le_log (by linarith : 0 < D) hstop
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

/-- No auxiliary error is needed for a stopped lower branch, at any depth. -/
theorem rosserPartialDefect_stopped_le_lowerError (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (R z : ℕ) (D : ℝ) (hD : 1 < D) (hz : 2 ≤ z) (hstop : D ≤ (z : ℝ) ^ 2) :
    rosserPartialDefect P R z false D ≤ lowerContinuousError (sieveParameter D z) := by
  have hzR : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have h := one_le_lowerContinuousError_of_le_two _ (sieveParameter_pos hD hzR)
    (sieveParameter_le_two_of_stop hD hzR hstop)
  cases R with
  | zero => simpa [rosserPartialDefect] using (le_trans (by norm_num : (0 : ℝ) ≤ 1) h)
  | succ R => simpa [rosserPartialDefect_recursion P hP hodd, hstop] using h

theorem rosserRelativeDefect_stopped_le_lowerError (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (z : ℕ) (D : ℝ) (hD : 1 < D) (hz : 2 ≤ z) (hstop : D ≤ (z : ℝ) ^ 2) :
    rosserRelativeDefect P z false D ≤ lowerContinuousError (sieveParameter D z) := by
  have h := rosserPartialDefect_stopped_le_lowerError P hP hodd (z + 1) z D hD hz hstop
  rwa [rosserPartialDefect_eq_defect P (z + 1) z false D (by omega)] at h

end Chen.LinearSieve
