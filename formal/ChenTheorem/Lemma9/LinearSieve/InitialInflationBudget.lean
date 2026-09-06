import ChenTheorem.Lemma9.LinearSieve.GrowingPrefixCutoff
import ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryError

open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem auxiliaryInflation_initial_bound (d D s : ℝ) (hd : 0 ≤ d)
    (hD : 1 < D) (hL : (4 : ℝ) ^ d ≤ Real.log D) (hs : 0 ≤ s) (hs4 : s ≤ 4) :
    auxiliaryInflation d D s ≤ 1 + 15 * (4 : ℝ) ^ d / Real.log D := by
  have hmono := monotoneOn_auxiliaryInflation d D hd hD hs (by norm_num) hs4
  have hlog := Real.log_pos hD
  let x := (4 : ℝ) ^ d / Real.log D
  have hx0 : 0 ≤ x := div_nonneg (Real.rpow_nonneg (by norm_num) d) hlog.le
  have hx1 : x ≤ 1 := (div_le_one hlog).mpr hL
  have hx2 : x ^ 2 ≤ x := by nlinarith
  have hx3 : x ^ 3 ≤ x := by
    have h := mul_le_mul_of_nonneg_right hx2 hx0
    nlinarith
  have hx4 : x ^ 4 ≤ x := by
    have h := mul_le_mul hx2 hx2 (sq_nonneg x) hx0
    nlinarith
  have hp : (1 + x) ^ (4 : ℕ) ≤ 1 + 15 * x := by nlinarith
  apply hmono.trans
  unfold auxiliaryInflation
  rw [Real.rpow_ofNat]
  convert! hp using 1
  dsimp [x]
  ring

theorem eventually_auxiliaryInflation_initial_small (d ε : ℝ) (hd : 1 < d) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 4 →
      auxiliaryInflation d D s ≤ 1 + ε / growingSieveParameter d (Real.log D) := by
  have hlim := ((tendsto_growingSieveParameter_div_self d hd).const_mul (15 * (4 : ℝ) ^ d)).comp Real.tendsto_log_atTop
  simp only [mul_zero] at hlim
  filter_upwards [eventually_growingPrefixCutoff_properties d hd,
    Real.tendsto_log_atTop.eventually_ge_atTop ((4 : ℝ) ^ d),
    hlim.eventually (gt_mem_nhds hε)] with D hc hL hb
  rcases hc with ⟨hD, hlog, hw, hm, hlo, hhi, hlevel⟩
  dsimp only [Function.comp_def] at hb
  have hσ := growingSieveParameter_pos d (Real.log D) hlog
  have hsmall : 15 * (4 : ℝ) ^ d / Real.log D ≤ ε / growingSieveParameter d (Real.log D) := by
    apply (le_div_iff₀ hσ).mpr
    convert! hb.le using 1
    ring
  refine ⟨hD, ?_⟩
  intro s hs hs4
  exact (auxiliaryInflation_initial_bound d D s (by linarith) hD hL hs hs4).trans
    (_root_.add_le_add le_rfl hsmall)

/-- Transfer of the weighted upper error costs only the inflation at the
larger parameter. The auxiliary weighted square itself is antitone. -/
theorem inflatedUpperError_weighted_transfer (d δ D s t : ℝ)
    (hD : 1 < D) (hs : 1 < s) (hst : s ≤ t) :
    t * inflatedAuxiliaryError d δ D t upperAuxiliaryError ≤
      auxiliaryInflation d D t * (s * inflatedAuxiliaryError d δ D s upperAuxiliaryError) := by
  have ht : 1 < t := hs.trans_le hst
  have hshape := antitoneOn_sq_mul_upperAuxiliaryError hs ht hst
  have hn : 0 ≤ s ^ 2 * upperAuxiliaryError s := mul_nonneg (sq_nonneg _) (upperAuxiliaryError_nonneg s hs)
  have hi := le_mul_of_one_le_left hn (one_le_auxiliaryInflation d D s hD (by linarith))
  have h := mul_le_mul_of_nonneg_left (hshape.trans hi)
    (mul_nonneg (auxiliaryInflation_pos d D t hD (by linarith)).le (Real.rpow_nonneg (Real.log_pos hD).le (-δ)))
  unfold inflatedAuxiliaryError auxiliaryErrorScale
  convert! h using 1 <;> ring

theorem eventually_inflatedUpperError_initial_transfer (d δ ε : ℝ) (hd : 1 < d) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ s t : ℝ, 1 < s → s ≤ t → t ≤ 4 →
      t * inflatedAuxiliaryError d δ D t upperAuxiliaryError ≤
        (1 + ε / growingSieveParameter d (Real.log D)) *
          (s * inflatedAuxiliaryError d δ D s upperAuxiliaryError) := by
  filter_upwards [eventually_auxiliaryInflation_initial_small d ε hd hε] with D hD
  refine ⟨hD.1, ?_⟩
  intro s t hs hst ht4
  apply (inflatedUpperError_weighted_transfer d δ D s t hD.1 hs hst).trans
  apply mul_le_mul_of_nonneg_right (hD.2 t (by linarith) ht4)
  exact mul_nonneg (by linarith) (inflatedAuxiliaryError_nonneg d δ D s upperAuxiliaryError hD.1
    (by linarith) (upperAuxiliaryError_nonneg s hs))

end Chen.LinearSieve
