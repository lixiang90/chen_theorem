import ChenTheorem.Analysis.DiskZeroLogDerivative

open Set Metric Function MeromorphicOn
open scoped Classical

namespace Chen

theorem zero_of_mem_disk_divisor_support {f : ℂ → ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) {w : ℂ}
    (hw : w ∈ (divisor f (ball 0 R)).support) : f w = 0 := by
  by_contra hne
  have hwR := (divisor f (ball 0 R)).supportWithinDomain hw
  exact ne_zero_point_ne_divisor_support hf (ball_subset_closedBall hwR) hne hw rfl

theorem one_le_disk_divisor_of_zero {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    {w : ℂ} (hw : w ∈ ball 0 R) (hfw : f w = 0) : 1 ≤ divisor f (ball 0 R) w := by
  have hm : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have horder0 : meromorphicOrderAt f 0 ≠ ⊤ := by
    rw [(hf 0 hm).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]
    simp
  have horder := hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (convex_closedBall (0 : ℂ) R).isPreconnected hm (ball_subset_closedBall hw) horder0
  have ho : meromorphicOrderAt f w ≠ 0 := by
    intro he
    exact ((hf w (ball_subset_closedBall hw)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp he) hfw
  have hd := (hf.mono ball_subset_closedBall).divisor_nonneg w
  change (0 : ℤ) ≤ divisor f (ball 0 R) w at hd
  have hdne : divisor f (ball 0 R) w ≠ 0 := by
    rw [(hf.mono ball_subset_closedBall).meromorphicOn.divisor_apply hw]
    intro he
    exact (WithTop.untop₀_eq_zero.mp he).elim ho horder
  omega

theorem re_int_zero_pole_nonneg (m : ℤ) (hm : 0 ≤ m) {z w : ℂ}
    (hzw : w.re ≤ z.re) : 0 ≤ ((m : ℂ) / (z - w)).re := by
  simp only [Complex.div_re, Complex.intCast_re, Complex.intCast_im, Complex.sub_re,
    zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg (by exact_mod_cast hm) (sub_nonneg.mpr hzw))
    (Complex.normSq_nonneg _)

theorem diskZeroPoleSum_re_nonneg {f : ℂ → ℂ} {R κ : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hright : ∀ w ∈ ball 0 R, κ < w.re → f w ≠ 0)
    {z : ℂ} (hz : κ ≤ z.re) : 0 ≤ (diskZeroPoleSum f R z).re := by
  let hfin := hf.meromorphicOn.divisor_ball_support_finite
  rw [diskZeroPoleSum_eq_sum f R hfin z, Complex.re_sum]
  apply Finset.sum_nonneg
  intro w hw
  have hws := hfin.mem_toFinset.mp hw
  have hwR := (divisor f (ball 0 R)).supportWithinDomain hws
  have hfw := zero_of_mem_disk_divisor_support hf hws
  have hwκ : w.re ≤ κ := le_of_not_gt (fun h => hright w hwR h hfw)
  exact re_int_zero_pole_nonneg _ ((hf.mono ball_subset_closedBall).divisor_nonneg w) (hwκ.trans hz)

theorem one_div_re_gap_le_re_zero_pole (m : ℤ) (hm : 1 ≤ m) {z w : ℂ}
    (hre : w.re < z.re) (him : w.im = z.im) :
    1 / (z.re - w.re) ≤ ((m : ℂ) / (z - w)).re := by
  have he : z - w = ((z.re - w.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [he, ← Complex.ofReal_intCast, ← Complex.ofReal_div, Complex.ofReal_re]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hm) (sub_nonneg.mpr hre.le)

/-- A zero at the same height as the evaluation point contributes at least
one reciprocal horizontal gap; the other zero contributions are nonnegative. -/
theorem one_div_re_gap_le_diskZeroPoleSum_re {f : ℂ → ℂ} {R κ : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    (hright : ∀ u ∈ ball 0 R, κ < u.re → f u ≠ 0)
    {z w : ℂ} (hz : κ < z.re) (hw : w ∈ ball 0 R) (hfw : f w = 0)
    (him : w.im = z.im) : 1 / (z.re - w.re) ≤ (diskZeroPoleSum f R z).re := by
  let hfin := hf.meromorphicOn.divisor_ball_support_finite
  have hmult := one_le_disk_divisor_of_zero hR hf h0 hw hfw
  have hws : w ∈ (divisor f (ball 0 R)).support := by
    apply mem_support.mpr
    omega
  have hwκ : w.re ≤ κ := le_of_not_gt (fun h => hright w hw h hfw)
  rw [diskZeroPoleSum_eq_sum f R hfin z, Complex.re_sum]
  apply (one_div_re_gap_le_re_zero_pole _ hmult (hwκ.trans_lt hz) him).trans
  apply Finset.single_le_sum _ (hfin.mem_toFinset.mpr hws)
  intro u hu
  have hus := hfin.mem_toFinset.mp hu
  have huR := (divisor f (ball 0 R)).supportWithinDomain hus
  have hfu := zero_of_mem_disk_divisor_support hf hus
  have huκ : u.re ≤ κ := le_of_not_gt (fun h => hright u huR h hfu)
  exact re_int_zero_pole_nonneg _ ((hf.mono ball_subset_closedBall).divisor_nonneg u) (huκ.trans hz.le)

end Chen
