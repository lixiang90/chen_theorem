import Submission.ChenTheorem.Analysis.ZeroPoleRealPart

set_option autoImplicit true
open Set Metric Function MeromorphicOn
open scoped Classical

namespace Chen

theorem two_le_disk_divisor_of_zero_deriv {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    {w : ℂ} (hw : w ∈ ball 0 R) (hfw : f w = 0) (hdfw : deriv f w = 0) :
    2 ≤ divisor f (ball 0 R) w := by
  have hd := one_le_disk_divisor_of_zero hR hf h0 hw hfw
  by_contra! hh
  have hd1 : divisor f (ball 0 R) w = 1 := by omega
  rw [(hf.mono ball_subset_closedBall).meromorphicOn.divisor_apply hw] at hd1
  have ho : meromorphicOrderAt f w = ((1 : ℤ) : WithTop ℤ) := by
    cases he : meromorphicOrderAt f w with
    | top => simp [he] at hd1
    | coe n => simpa [he] using hd1
  have hdo := meromorphicOrderAt_deriv_eq_sub_one (f := f) (x := w) (n := (1 : ℤ)) (by norm_num) ho
  norm_num at hdo
  have hdne := ((hf w (ball_subset_closedBall hw)).deriv.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mp hdo
  exact hdne hdfw

theorem two_div_re_gap_le_diskZeroPoleSum_re_of_zero_deriv {f : ℂ → ℂ} {R κ : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    (hright : ∀ u ∈ ball 0 R, κ < u.re → f u ≠ 0)
    {z w : ℂ} (hz : κ < z.re) (hw : w ∈ ball 0 R) (hfw : f w = 0)
    (hdfw : deriv f w = 0) (him : w.im = z.im) :
    2 / (z.re - w.re) ≤ (diskZeroPoleSum f R z).re := by
  let hfin := hf.meromorphicOn.divisor_ball_support_finite
  have hm := two_le_disk_divisor_of_zero_deriv hR hf h0 hw hfw hdfw
  have hws : w ∈ (divisor f (ball 0 R)).support := by apply mem_support.mpr; omega
  have hwκ : w.re ≤ κ := le_of_not_gt (fun h => hright w hw h hfw)
  have he : z - w = ((z.re - w.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hp : 2 / (z.re - w.re) ≤ (((divisor f (ball 0 R) w : ℤ) : ℂ) / (z - w)).re := by
    rw [he, ← Complex.ofReal_intCast, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hm) (by linarith)
  rw [diskZeroPoleSum_eq_sum f R hfin z, Complex.re_sum]
  apply hp.trans
  apply Finset.single_le_sum _ (hfin.mem_toFinset.mpr hws)
  intro u hu
  have hus := hfin.mem_toFinset.mp hu
  have huR := (divisor f (ball 0 R)).supportWithinDomain hus
  have hfu := zero_of_mem_disk_divisor_support hf hus
  have huκ : u.re ≤ κ := le_of_not_gt (fun h => hright u huR h hfu)
  exact re_int_zero_pole_nonneg _ ((hf.mono ball_subset_closedBall).divisor_nonneg u) (huκ.trans hz.le)

end Chen
