import Submission.ChenTheorem.Analysis.DiskZeroLogDerivative
import Submission.ChenTheorem.Analysis.ZeroFreeFactorBounds

set_option autoImplicit true
open Set Metric Filter Topology

namespace Chen

theorem logDeriv_eq_blaschke_add_factor {f g : ℂ → ℂ} {R : ℝ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (he : EqOn f (fun z => diskBlaschkeProduct f R z * g z) (closedBall 0 R))
    {z : ℂ} (hz : z ∈ ball 0 R) (hfz : f z ≠ 0) (hgz : g z ≠ 0) :
    logDeriv f z = logDeriv (diskBlaschkeProduct f R) z + logDeriv g z := by
  have hzR := ball_subset_closedBall hz
  have hn : closedBall (0 : ℂ) R ∈ 𝓝 z :=
    mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall
  have he' := he.eventuallyEq_of_mem hn
  have hpz : diskBlaschkeProduct f R z ≠ 0 := by
    intro hp
    apply hfz
    calc
      f z = diskBlaschkeProduct f R z * g z := he hzR
      _ = 0 := by rw [hp, zero_mul]
  have hp := (analyticOnNhd_diskBlaschkeProduct f R z hzR).differentiableAt
  calc
    logDeriv f z = logDeriv (fun u => diskBlaschkeProduct f R u * g u) z := by
      rw [logDeriv_apply, logDeriv_apply, he'.deriv_eq, he hzR]
    _ = _ := logDeriv_mul z hpz hgz hp (hg z hzR).differentiableAt

/-- Local zero isolation: subtracting the poles of the zeros in the disk
leaves an error bounded by boundary growth and the number of zeros. -/
theorem norm_logDeriv_sub_diskZeroPoleSum_le {f : ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hB : 0 < B) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (h0 : f 0 ≠ 0) (hb : ∀ w ∈ sphere 0 R, ‖f w‖ ≤ Real.exp B * ‖f 0‖)
    {z : ℂ} (hz : ‖z‖ ≤ 3 * R / 4) (hfz : f z ≠ 0) :
    ‖deriv f z / f z - diskZeroPoleSum f R z‖ ≤ (224 * B + 4 * diskZeroCount f R) / R := by
  obtain ⟨g, hg, hne, he, hgbound⟩ := exists_analytic_factor_with_logDeriv_bound hR hB hf h0 hb
  have hzR : z ∈ ball 0 R := by simp only [mem_ball_zero_iff]; linarith
  have hlog := logDeriv_eq_blaschke_add_factor hg he hzR hfz (hne z hzR)
  have hpb := norm_logDeriv_diskBlaschkeProduct_sub_poles_le hR hf hz hfz
  have hgb := hgbound z hz
  change ‖logDeriv f z - diskZeroPoleSum f R z‖ ≤ _
  rw [hlog, show logDeriv (diskBlaschkeProduct f R) z + logDeriv g z - diskZeroPoleSum f R z =
    (logDeriv (diskBlaschkeProduct f R) z - diskZeroPoleSum f R z) + logDeriv g z by ring]
  apply (norm_add_le _ _).trans
  calc
    _ ≤ (4 / R) * diskZeroCount f R + 224 * B / R := add_le_add hpb hgb
    _ = _ := by ring

end Chen
