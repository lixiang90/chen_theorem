import ChenTheorem.Analysis.DiskZeroLogDerivative
import Mathlib.Analysis.Complex.JensenFormula

open Set Metric Function MeromorphicOn

namespace Chen

theorem diskZeroCount_nonneg {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) : 0 ≤ diskZeroCount f R := by
  apply finsum_nonneg
  intro w
  exact_mod_cast (hf.mono ball_subset_closedBall).divisor_nonneg w

theorem diskZeroCount_le_closedBall {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    diskZeroCount f R ≤ ((∑ᶠ w, divisor f (closedBall 0 R) w : ℤ) : ℝ) := by
  have hfin := (divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
  have hmap : ((∑ᶠ w, divisor f (closedBall 0 R) w : ℤ) : ℝ) =
      ∑ᶠ w, (divisor f (closedBall 0 R) w : ℝ) := map_finsum (Int.castRingHom ℝ) hfin
  rw [hmap]
  apply finsum_le_finsum'
  · apply hf.meromorphicOn.divisor_ball_support_finite.subset
    intro w hw
    simpa only [mem_support, ne_eq, Int.cast_eq_zero] using hw
  · apply hfin.subset
    intro w hw
    simpa only [mem_support, ne_eq, Int.cast_eq_zero] using hw
  · intro w
    change (divisor f (ball 0 R) w : ℝ) ≤ (divisor f (closedBall 0 R) w : ℝ)
    by_cases hw : w ∈ ball 0 R
    · rw [(hf.mono ball_subset_closedBall).meromorphicOn.divisor_apply hw,
        hf.meromorphicOn.divisor_apply (ball_subset_closedBall hw)]
    · rw [locallyFinsuppWithin.apply_eq_zero_of_notMem _ hw, Int.cast_zero]
      exact_mod_cast hf.divisor_nonneg w

theorem diskZeroCount_le_of_outer_bound {f : ℂ → ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    (hb : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ M) :
    diskZeroCount f r ≤ Real.log (M / ‖f 0‖) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hf' : AnalyticOnNhd ℂ f (closedBall 0 |R|) := by simpa only [abs_of_pos hR] using hf
  have hb' : ∀ z ∈ sphere 0 |R|, ‖f z‖ ≤ M := by simpa only [abs_of_pos hR] using hb
  have hj := hf'.sum_divisor_le (r := r) (R := R)
    (by simpa only [abs_of_pos hr] using hr)
    (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR) hM h0 hb'
  rw [abs_of_pos hr] at hj
  exact (diskZeroCount_le_closedBall (hf.mono (closedBall_subset_closedBall hrR.le))).trans hj

end Chen
