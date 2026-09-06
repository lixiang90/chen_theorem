import ChenTheorem.Analysis.ZeroPoleRealPart

open Set Metric MeromorphicOn Function

namespace Chen

theorem re_one_zero_pole_le_int_zero_pole (m : ℤ) (hm : 1 ≤ m) {z w : ℂ}
    (hre : w.re ≤ z.re) : (1 / (z - w)).re ≤ ((m : ℂ) / (z - w)).re := by
  simp only [Complex.div_re, Complex.one_re, Complex.one_im, Complex.intCast_re,
    Complex.intCast_im, Complex.sub_re, zero_mul, zero_div, add_zero, one_mul]
  apply div_le_div_of_nonneg_right _ (Complex.normSq_nonneg _)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- Any finite set of distinct zeros gives a lower bound for the real part
of the full pole sum. Multiplicities in the full sum are at least one. -/
theorem sum_re_zero_poles_le_diskZeroPoleSum_re {f : ℂ → ℂ} {R κ : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    (hright : ∀ u ∈ ball 0 R, κ < u.re → f u ≠ 0)
    {z : ℂ} (hz : κ ≤ z.re) (T : Finset ℂ)
    (hT : ∀ w ∈ T, w ∈ ball 0 R ∧ f w = 0) :
    ∑ w ∈ T, (1 / (z - w)).re ≤ (diskZeroPoleSum f R z).re := by
  classical
  let hfin := hf.meromorphicOn.divisor_ball_support_finite
  have hsub : T ⊆ hfin.toFinset := by
    intro w hw
    apply hfin.mem_toFinset.mpr
    apply mem_support.mpr
    have hm := one_le_disk_divisor_of_zero hR hf h0 (hT w hw).1 (hT w hw).2
    omega
  have hnonneg : ∀ w ∈ hfin.toFinset,
      0 ≤ (((divisor f (ball 0 R) w : ℤ) : ℂ) / (z - w)).re := by
    intro w hw
    have hws := hfin.mem_toFinset.mp hw
    have hwR := (divisor f (ball 0 R)).supportWithinDomain hws
    have hfw := zero_of_mem_disk_divisor_support hf hws
    have hwκ : w.re ≤ κ := le_of_not_gt (fun h => hright w hwR h hfw)
    exact re_int_zero_pole_nonneg _ ((hf.mono ball_subset_closedBall).divisor_nonneg w)
      (hwκ.trans hz)
  rw [diskZeroPoleSum_eq_sum f R hfin z, Complex.re_sum]
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w hw _ => hnonneg w hw))
  apply Finset.sum_le_sum
  intro w hw
  have hwκ : w.re ≤ κ := le_of_not_gt (fun h => hright w (hT w hw).1 h (hT w hw).2)
  exact re_one_zero_pole_le_int_zero_pole _
    (one_le_disk_divisor_of_zero hR hf h0 (hT w hw).1 (hT w hw).2) (hwκ.trans hz)

theorem pair_re_zero_poles_le_diskZeroPoleSum_re {f : ℂ → ℂ} {R κ : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0)
    (hright : ∀ u ∈ ball 0 R, κ < u.re → f u ≠ 0)
    {z w₁ w₂ : ℂ} (hz : κ ≤ z.re) (hw₁ : w₁ ∈ ball 0 R) (hw₂ : w₂ ∈ ball 0 R)
    (hf₁ : f w₁ = 0) (hf₂ : f w₂ = 0) (hne : w₁ ≠ w₂) :
    (1 / (z - w₁)).re + (1 / (z - w₂)).re ≤ (diskZeroPoleSum f R z).re := by
  classical
  have h := sum_re_zero_poles_le_diskZeroPoleSum_re hR hf h0 hright hz {w₁, w₂}
    (by intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact ⟨hw₁, hf₁⟩
        · exact ⟨hw₂, hf₂⟩)
  simpa [hne] using h

end Chen
