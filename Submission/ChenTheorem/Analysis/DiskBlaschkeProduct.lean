import Submission.ChenTheorem.Analysis.BlaschkeFactor

set_option autoImplicit true
open Set Metric Function MeromorphicOn
open scoped Classical

namespace Chen

/-- The finite Blaschke product of the zeros in the open disk, with their
analytic multiplicities. The support is finite when `f` is analytic on the closed disk. -/
noncomputable def diskBlaschkeProduct (f : ℂ → ℂ) (R : ℝ) : ℂ → ℂ :=
  ∏ᶠ w, (blaschkeFactor R w) ^ (divisor f (ball 0 R) w).toNat

theorem diskBlaschkeProduct_eq_prod (f : ℂ → ℂ) (R : ℝ)
    (hfin : (divisor f (ball 0 R)).support.Finite) (z : ℂ) :
    diskBlaschkeProduct f R z = ∏ w ∈ hfin.toFinset,
      blaschkeFactor R w z ^ (divisor f (ball 0 R) w).toNat := by
  have hs : (fun w => (blaschkeFactor R w) ^ (divisor f (ball 0 R) w).toNat).mulSupport ⊆
      (divisor f (ball 0 R)).support := by
    intro w hw
    contrapose! hw
    simp only [mem_support, not_not] at hw
    simp [hw]
  rw [diskBlaschkeProduct, finprod_eq_prod_of_mulSupport_subset_of_finite _ hs hfin]
  simp

theorem analyticOnNhd_diskBlaschkeProduct (f : ℂ → ℂ) (R : ℝ) :
    AnalyticOnNhd ℂ (diskBlaschkeProduct f R) (closedBall 0 R) := by
  intro z hz
  apply analyticAt_finprod
  intro w
  by_cases hw : w ∈ ball 0 R
  · exact ((analyticOnNhd_blaschkeFactor hw) z hz).pow _
  · simp only [locallyFinsuppWithin.apply_eq_zero_of_notMem _ hw, Int.toNat_zero, pow_zero]
    exact analyticAt_const

theorem norm_diskBlaschkeProduct_le_one (f : ℂ → ℂ) (R : ℝ)
    (hfin : (divisor f (ball 0 R)).support.Finite) {z : ℂ} (hz : z ∈ closedBall 0 R) :
    ‖diskBlaschkeProduct f R z‖ ≤ 1 := by
  rw [diskBlaschkeProduct_eq_prod f R hfin z, norm_prod]
  apply Finset.prod_le_one
  · intro w hw
    positivity
  · intro w hw
    rw [norm_pow]
    have hwR := (divisor f (ball 0 R)).supportWithinDomain (hfin.mem_toFinset.mp hw)
    exact pow_le_one₀ (norm_nonneg _) (norm_blaschkeFactor_le_one hwR hz)

theorem norm_diskBlaschkeProduct_on_sphere (f : ℂ → ℂ) (R : ℝ)
    (hfin : (divisor f (ball 0 R)).support.Finite) {z : ℂ} (hz : z ∈ sphere 0 R) :
    ‖diskBlaschkeProduct f R z‖ = 1 := by
  rw [diskBlaschkeProduct_eq_prod f R hfin z, norm_prod]
  apply Finset.prod_eq_one
  intro w hw
  have hwR := (divisor f (ball 0 R)).supportWithinDomain (hfin.mem_toFinset.mp hw)
  rw [norm_pow, norm_blaschkeFactor_on_sphere hwR hz, one_pow]

theorem canonical_product_eq_diskBlaschkeProduct {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    (∏ᶠ w, (Complex.canonicalFactor R w) ^ (-divisor f (ball 0 R) w)) =
      diskBlaschkeProduct f R := by
  unfold diskBlaschkeProduct
  congr 1
  funext w z
  have hd : 0 ≤ divisor f (ball 0 R) w := (hf.mono ball_subset_closedBall).divisor_nonneg w
  have he : ((divisor f (ball 0 R) w).toNat : ℤ) = divisor f (ball 0 R) w :=
    Int.toNat_of_nonneg hd
  simp only [Pi.pow_apply]
  conv_lhs => rw [← he]
  rw [zpow_neg, zpow_natCast, blaschkeFactor_eq_inv_canonicalFactor, inv_pow]

end Chen
