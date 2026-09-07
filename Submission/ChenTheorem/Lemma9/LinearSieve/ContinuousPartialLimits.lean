import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousErrors

set_option autoImplicit true
open Filter Finset Set
open scoped Topology

namespace Chen.LinearSieve

theorem tendsto_upperContinuousPartial (s : ℝ) (hs : 1 < s) :
    Tendsto (fun N => upperContinuousPartial N s) atTop (𝓝 (upperContinuousError s)) := by
  exact (summable_odd_rosserContinuousTerm s hs).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)

theorem tendsto_lowerContinuousPartial (s : ℝ) (hs : 2 ≤ s) :
    Tendsto (fun N => lowerContinuousPartial N s) atTop (𝓝 (lowerContinuousError s)) :=
  (summable_even_rosserContinuousTerm s hs).hasSum.tendsto_sum_nat

theorem antitoneOn_upperContinuousError : AntitoneOn upperContinuousError (Ioi 1) := by
  intro s hs t ht hst
  exact (summable_odd_rosserContinuousTerm t ht).tsum_le_tsum
    (fun N => antitoneOn_rosserContinuousTerm _ (show 0 < s by linarith [show 1 < s from hs])
      (show 0 < t by linarith [show 1 < t from ht]) hst)
    (summable_odd_rosserContinuousTerm s hs)

theorem antitoneOn_lowerContinuousError : AntitoneOn lowerContinuousError (Ici 2) := by
  intro s hs t ht hst
  exact (summable_even_rosserContinuousTerm t ht).tsum_le_tsum
    (fun N => antitoneOn_rosserContinuousTerm _ (show 0 < s by linarith [show 2 ≤ s from hs])
      (show 0 < t by linarith [show 2 ≤ t from ht]) hst)
    (summable_even_rosserContinuousTerm s hs)

end Chen.LinearSieve
