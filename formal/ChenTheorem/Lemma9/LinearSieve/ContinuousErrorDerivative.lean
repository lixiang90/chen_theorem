import ChenTheorem.Lemma9.LinearSieve.ContinuousErrors
import Mathlib.Analysis.Calculus.SmoothSeries

open Finset Set Filter

namespace Chen.LinearSieve

theorem summable_odd_rosserContinuousTerm_tail (s : ℝ) (hs : 1 < s) :
    Summable (fun N => rosserContinuousTerm (2 * N + 3) s) := by
  have h := (summable_odd_rosserContinuousTerm s hs).comp_injective Nat.succ_injective
  convert! h using 1

theorem upperContinuousError_eq_tsum_tail (s : ℝ) (hs : 3 < s) :
    upperContinuousError s = ∑' N, rosserContinuousTerm (2 * N + 3) s := by
  unfold upperContinuousError
  rw [(summable_odd_rosserContinuousTerm s (by linarith)).tsum_eq_zero_add]
  simp only [Nat.mul_zero, zero_add]
  rw [rosserContinuousTerm_eq_zero 1 s (by norm_num; linarith), zero_add]
  apply tsum_congr
  intro N
  congr 1

/-- The lower error's delay equation. Uniform summable bounds on the
derivatives justify differentiating the infinite series. -/
theorem hasDerivAt_mul_lowerContinuousError (s : ℝ) (hs : 2 < s) :
    HasDerivAt (fun s => s * lowerContinuousError s) (-upperContinuousError (s - 1)) s := by
  let a : ℝ := (s + 2) / 2
  have ha : 2 < a := by dsimp [a]; linarith
  have has : a < s := by dsimp [a]; linarith
  have hu := summable_odd_rosserContinuousTerm (a - 1) (by linarith)
  have hg : ∀ N y, y ∈ Ioi a →
      HasDerivAt (fun y => y * rosserContinuousTerm (2 * N + 2) y)
        (-rosserContinuousTerm (2 * N + 1) (y - 1)) y := by
    intro N y hy
    apply hasDerivAt_mul_rosserContinuousTerm (2 * N) y
    have hc : rosserContinuousCutoff (2 * N + 2) = 2 := by
      simp [rosserContinuousCutoff, Nat.even_add]
    rw [hc]
    exact ha.trans hy
  have hbound : ∀ N y, y ∈ Ioi a →
      ‖-rosserContinuousTerm (2 * N + 1) (y - 1)‖ ≤
        rosserContinuousTerm (2 * N + 1) (a - 1) := by
    intro N y hy
    rw [norm_neg]
    exact norm_rosserContinuousTerm_le _ _ _ (by linarith) (sub_le_sub_right hy.le 1)
  have h := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi (convex_Ioi a).isPreconnected
    hg hbound (show s ∈ Ioi a from has)
    ((summable_even_rosserContinuousTerm s hs.le).mul_left s) (show s ∈ Ioi a from has)
  simpa only [tsum_mul_left, tsum_neg, upperContinuousError, lowerContinuousError] using h

/-- The upper error's delay equation on the interval beyond its lower
cutoff. The first odd term vanishes here and the remaining derivatives
are dominated by the already convergent even series. -/
theorem hasDerivAt_mul_upperContinuousError (s : ℝ) (hs : 3 < s) :
    HasDerivAt (fun s => s * upperContinuousError s) (-lowerContinuousError (s - 1)) s := by
  let a : ℝ := (s + 3) / 2
  have ha : 3 < a := by dsimp [a]; linarith
  have has : a < s := by dsimp [a]; linarith
  have hu := summable_even_rosserContinuousTerm (a - 1) (by linarith)
  have hg : ∀ N y, y ∈ Ioi a →
      HasDerivAt (fun y => y * rosserContinuousTerm (2 * N + 3) y)
        (-rosserContinuousTerm (2 * N + 2) (y - 1)) y := by
    intro N y hy
    have hc : rosserContinuousCutoff (2 * N + 1 + 2) < y := by
      simp only [rosserContinuousCutoff]
      have he : ¬Even (2 * N + 1 + 2) := by simp [Nat.even_add]
      rw [if_neg he]
      exact ha.trans hy
    convert! hasDerivAt_mul_rosserContinuousTerm (2 * N + 1) y hc using 1
  have hbound : ∀ N y, y ∈ Ioi a →
      ‖-rosserContinuousTerm (2 * N + 2) (y - 1)‖ ≤
        rosserContinuousTerm (2 * N + 2) (a - 1) := by
    intro N y hy
    rw [norm_neg]
    exact norm_rosserContinuousTerm_le _ _ _ (by linarith) (sub_le_sub_right hy.le 1)
  have h := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi (convex_Ioi a).isPreconnected
    hg hbound (show s ∈ Ioi a from has)
    ((summable_odd_rosserContinuousTerm_tail s (by linarith)).mul_left s)
    (show s ∈ Ioi a from has)
  have h' : HasDerivAt (fun y => y * ∑' N, rosserContinuousTerm (2 * N + 3) y)
      (-lowerContinuousError (s - 1)) s := by
    simpa only [tsum_mul_left, tsum_neg, lowerContinuousError] using h
  apply h'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with y hy
  rw [upperContinuousError_eq_tsum_tail y hy]

end Chen.LinearSieve
