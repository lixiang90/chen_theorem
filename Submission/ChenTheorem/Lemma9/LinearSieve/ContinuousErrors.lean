import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option autoImplicit true

open Finset Set Filter

namespace Chen.LinearSieve

/-- The convergent odd-term error of the upper linear sieve, used for `s>1`. -/
noncomputable def upperContinuousError (s : ℝ) : ℝ :=
  ∑' N, rosserContinuousTerm (2 * N + 1) s

/-- The convergent even-term error of the lower linear sieve, used for `s≥2`. -/
noncomputable def lowerContinuousError (s : ℝ) : ℝ :=
  ∑' N, rosserContinuousTerm (2 * N + 2) s

theorem upperContinuousError_bounds (s : ℝ) (hs : 1 < s) :
    0 ≤ upperContinuousError s ∧ upperContinuousError s ≤ 2 / (min s 2 - 1) :=
  ⟨tsum_nonneg (fun N => rosserContinuousTerm_nonneg _ s (by linarith)),
    tsum_odd_rosserContinuousTerm_le s hs⟩

theorem lowerContinuousError_bounds (s : ℝ) (hs : 2 ≤ s) :
    0 ≤ lowerContinuousError s ∧ lowerContinuousError s ≤ 1 :=
  ⟨tsum_nonneg (fun N => rosserContinuousTerm_nonneg _ s (by linarith)),
    tsum_even_rosserContinuousTerm_le_one s hs⟩

theorem norm_rosserContinuousTerm_le (n : ℕ) (a s : ℝ) (ha : 0 < a) (has : a ≤ s) :
    ‖rosserContinuousTerm n s‖ ≤ rosserContinuousTerm n a := by
  rw [Real.norm_eq_abs, abs_of_nonneg (rosserContinuousTerm_nonneg n s (ha.trans_le has))]
  exact antitoneOn_rosserContinuousTerm n ha (ha.trans_le has) has

/-- Uniform convergence holds on each half-line bounded away from the
open endpoint of the odd series. -/
theorem tendstoUniformlyOn_upperContinuousError (a : ℝ) (ha : 1 < a) :
    TendstoUniformlyOn (fun N s => ∑ k ∈ range N, rosserContinuousTerm (2 * k + 1) s)
      upperContinuousError atTop (Ici a) := by
  exact tendstoUniformlyOn_tsum_nat (summable_odd_rosserContinuousTerm a ha)
    (fun N s hs => norm_rosserContinuousTerm_le _ a s (by linarith) hs)

theorem tendstoUniformlyOn_lowerContinuousError (a : ℝ) (ha : 2 ≤ a) :
    TendstoUniformlyOn (fun N s => ∑ k ∈ range N, rosserContinuousTerm (2 * k + 2) s)
      lowerContinuousError atTop (Ici a) := by
  exact tendstoUniformlyOn_tsum_nat (summable_even_rosserContinuousTerm a ha)
    (fun N s hs => norm_rosserContinuousTerm_le _ a s (by linarith) hs)

theorem continuousOn_upperContinuousError_Ici (a : ℝ) (ha : 1 < a) :
    ContinuousOn upperContinuousError (Ici a) := by
  exact continuousOn_tsum
    (fun N => (continuousOn_rosserContinuousTerm (2 * N + 1)).mono
      (fun s hs => by change 0 < s; linarith [show a ≤ s from hs]))
    (summable_odd_rosserContinuousTerm a ha)
    (fun N s hs => norm_rosserContinuousTerm_le _ a s (by linarith) hs)

theorem continuousOn_upperContinuousError : ContinuousOn upperContinuousError (Ioi 1) := by
  intro s hs
  have ha : 1 < (s + 1) / 2 := by linarith [show 1 < s from hs]
  have has : (s + 1) / 2 < s := by linarith [show 1 < s from hs]
  exact ((continuousOn_upperContinuousError_Ici _ ha s has.le).continuousAt
    (Ici_mem_nhds has)).continuousWithinAt

theorem continuousOn_lowerContinuousError : ContinuousOn lowerContinuousError (Ici 2) := by
  exact continuousOn_tsum
    (fun N => (continuousOn_rosserContinuousTerm (2 * N + 2)).mono
      (fun s hs => by change 0 < s; linarith [show 2 ≤ s from hs]))
    (summable_even_rosserContinuousTerm 2 le_rfl)
    (fun N s hs => norm_rosserContinuousTerm_le _ 2 s (by norm_num) hs)

theorem antitoneOn_mul_upperContinuousError :
    AntitoneOn (fun s => s * upperContinuousError s) (Ioi 1) := by
  intro s hs t ht hst
  dsimp only [upperContinuousError]
  rw [← tsum_mul_left, ← tsum_mul_left]
  exact ((summable_odd_rosserContinuousTerm t ht).mul_left t).tsum_le_tsum
    (fun N => antitoneOn_mul_rosserContinuousTerm (2 * N + 1)
      (by change 0 < s; linarith [show 1 < s from hs])
      (by change 0 < t; linarith [show 1 < t from ht]) hst)
    ((summable_odd_rosserContinuousTerm s hs).mul_left s)

theorem antitoneOn_mul_lowerContinuousError :
    AntitoneOn (fun s => s * lowerContinuousError s) (Ici 2) := by
  intro s hs t ht hst
  dsimp only [lowerContinuousError]
  rw [← tsum_mul_left, ← tsum_mul_left]
  exact ((summable_even_rosserContinuousTerm t ht).mul_left t).tsum_le_tsum
    (fun N => antitoneOn_mul_rosserContinuousTerm (2 * N + 2)
      (by change 0 < s; linarith [show 2 ≤ s from hs])
      (by change 0 < t; linarith [show 2 ≤ t from ht]) hst)
    ((summable_even_rosserContinuousTerm s hs).mul_left s)

end Chen.LinearSieve
