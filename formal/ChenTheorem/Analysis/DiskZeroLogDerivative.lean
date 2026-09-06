import ChenTheorem.Analysis.DiskBlaschkeProduct
import ChenTheorem.Analysis.BlaschkeLogDerivative

open Set Metric Function MeromorphicOn
open scoped Classical ComplexConjugate

namespace Chen

noncomputable def diskZeroPoleSum (f : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  ∑ᶠ w, (divisor f (ball 0 R) w : ℂ) / (z - w)

noncomputable def diskZeroCount (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  ∑ᶠ w, (divisor f (ball 0 R) w : ℝ)

theorem diskZeroPoleSum_eq_sum (f : ℂ → ℂ) (R : ℝ)
    (hfin : (divisor f (ball 0 R)).support.Finite) (z : ℂ) :
    diskZeroPoleSum f R z = ∑ w ∈ hfin.toFinset, (divisor f (ball 0 R) w : ℂ) / (z - w) := by
  apply finsum_eq_sum_of_support_subset_of_finite _ _ hfin
  intro w hw
  contrapose! hw
  simp only [mem_support, not_not] at hw
  simp [hw]

theorem diskZeroCount_eq_sum (f : ℂ → ℂ) (R : ℝ)
    (hfin : (divisor f (ball 0 R)).support.Finite) :
    diskZeroCount f R = ∑ w ∈ hfin.toFinset, (divisor f (ball 0 R) w : ℝ) := by
  apply finsum_eq_sum_of_support_subset_of_finite _ _ hfin
  intro w hw
  contrapose! hw
  simp only [mem_support, not_not] at hw
  simp [hw]

theorem ne_zero_point_ne_divisor_support {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) {z w : ℂ}
    (hz : z ∈ closedBall 0 R) (hfz : f z ≠ 0)
    (hw : w ∈ (divisor f (ball 0 R)).support) : z ≠ w := by
  intro he
  subst w
  have hzR := (divisor f (ball 0 R)).supportWithinDomain hw
  have ho := (hf z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfz
  have hd := mem_support.mp hw
  rw [(hf.mono ball_subset_closedBall).meromorphicOn.divisor_apply hzR, ho] at hd
  simp at hd

theorem logDeriv_diskBlaschkeProduct {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) {z : ℂ}
    (hz : z ∈ closedBall 0 R) (hfz : f z ≠ 0) :
    logDeriv (diskBlaschkeProduct f R) z =
      ∑ w ∈ hf.meromorphicOn.divisor_ball_support_finite.toFinset,
        (divisor f (ball 0 R) w : ℂ) *
          (1 / (z - w) + conj w / ((R : ℂ) ^ 2 - conj w * z)) := by
  let hfin := hf.meromorphicOn.divisor_ball_support_finite
  have hwR (w : ℂ) (hw : w ∈ hfin.toFinset) : w ∈ ball 0 R :=
    (divisor f (ball 0 R)).supportWithinDomain (hfin.mem_toFinset.mp hw)
  have hzw (w : ℂ) (hw : w ∈ hfin.toFinset) : z ≠ w :=
    ne_zero_point_ne_divisor_support hf hz hfz (hfin.mem_toFinset.mp hw)
  have hprod : diskBlaschkeProduct f R = fun u => ∏ w ∈ hfin.toFinset,
      blaschkeFactor R w u ^ (divisor f (ball 0 R) w).toNat := by
    funext u
    exact diskBlaschkeProduct_eq_prod f R hfin u
  rw [hprod, logDeriv_prod (s := hfin.toFinset)
    (f := fun w u => blaschkeFactor R w u ^ (divisor f (ball 0 R) w).toNat) (x := z)
    (fun w hw => pow_ne_zero _ (blaschkeFactor_ne_zero (hwR w hw) hz (hzw w hw)))
    (fun w hw => ((analyticOnNhd_blaschkeFactor (hwR w hw)) z hz).differentiableAt.pow _)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [logDeriv_fun_pow ((analyticOnNhd_blaschkeFactor (hwR w hw)) z hz).differentiableAt,
    logDeriv_blaschkeFactor (hwR w hw) hz (hzw w hw)]
  have hd := (hf.mono ball_subset_closedBall).divisor_nonneg w
  have hcast : ((divisor f (ball 0 R) w).toNat : ℂ) = (divisor f (ball 0 R) w : ℂ) := by
    exact_mod_cast Int.toNat_of_nonneg hd
  rw [hcast]

/-- The logarithmic derivative of the finite zero product equals the sum
of the zero poles up to a term controlled by the number of zeros. -/
theorem norm_logDeriv_diskBlaschkeProduct_sub_poles_le {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) {z : ℂ}
    (hz : ‖z‖ ≤ 3 * R / 4) (hfz : f z ≠ 0) :
    ‖logDeriv (diskBlaschkeProduct f R) z - diskZeroPoleSum f R z‖ ≤
      (4 / R) * diskZeroCount f R := by
  have hzR : z ∈ closedBall 0 R := by simp only [mem_closedBall_zero_iff]; linarith
  let hfin := hf.meromorphicOn.divisor_ball_support_finite
  rw [logDeriv_diskBlaschkeProduct hf hzR hfz, diskZeroPoleSum_eq_sum f R hfin z,
    ← Finset.sum_sub_distrib, diskZeroCount_eq_sum f R hfin, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro w hw
  have hwR := (divisor f (ball 0 R)).supportWithinDomain (hfin.mem_toFinset.mp hw)
  have hd := (hf.mono ball_subset_closedBall).divisor_nonneg w
  rw [show (divisor f (ball 0 R) w : ℂ) *
      (1 / (z - w) + conj w / ((R : ℂ) ^ 2 - conj w * z)) -
      (divisor f (ball 0 R) w : ℂ) / (z - w) =
      (divisor f (ball 0 R) w : ℂ) * (conj w / ((R : ℂ) ^ 2 - conj w * z)) by ring,
    norm_mul, Complex.norm_int_of_nonneg hd]
  have h := mul_le_mul_of_nonneg_left (norm_blaschke_logDeriv_correction_le hwR hz)
    (show (0 : ℝ) ≤ (divisor f (ball 0 R) w : ℝ) by exact_mod_cast hd)
  simpa only [mul_comm] using h

end Chen
