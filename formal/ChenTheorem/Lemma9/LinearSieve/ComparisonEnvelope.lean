import ChenTheorem.Lemma9.LinearSieve.RosserAuxiliaryComparison
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

open Set

namespace Chen.LinearSieve

noncomputable def comparisonEnvelope (M d δ L s : ℝ) : ℝ :=
  (2 * Real.log M + |δ| * Real.log L + |Real.log auxiliaryLowerConstant|) / s +
    2 * (Real.log s / s) + 8 + Real.log (1 + Real.log M) +
      Real.log (Real.log s) + Real.log L - d * Real.log s

theorem log_sub_mul_antitoneOn (d : ℝ) (hd : 1 ≤ d) :
    AntitoneOn (fun x : ℝ => Real.log x - d * x) (Ici 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by change 1 ≤ x at hx; linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [Real.log_div hy0.ne' hx0.ne'] at h
  have hdiv : y / x - 1 ≤ y - x := by
    rw [sub_le_iff_le_add, div_le_iff₀ hx0]
    have hm := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hx)
    nlinarith
  have hdif := mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hxy)
  dsimp only
  nlinarith

theorem comparisonEnvelope_antitoneOn (M d δ L : ℝ)
    (hM : 1 ≤ M) (hd : 1 ≤ d) (hL : 1 ≤ L) :
    AntitoneOn (comparisonEnvelope M d δ L) (Ici (Real.exp 1)) := by
  intro s hs t ht hst
  have hs0 : 0 < s := (Real.exp_pos 1).trans_le hs
  have ht0 : 0 < t := hs0.trans_le hst
  have hC : 0 ≤ 2 * Real.log M + |δ| * Real.log L + |Real.log auxiliaryLowerConstant| := by
    have := Real.log_nonneg hM
    have := Real.log_nonneg hL
    positivity
  have hdiv := div_le_div_of_nonneg_left hC hs0 hst
  have hlogdiv := Real.log_div_self_antitoneOn hs ht hst
  have hslog : 1 ≤ Real.log s := (Real.le_log_iff_exp_le hs0).2 hs
  have htlog : 1 ≤ Real.log t := (Real.le_log_iff_exp_le ht0).2 ht
  have hlogs := Real.log_le_log hs0 hst
  have hlast := log_sub_mul_antitoneOn d hd hslog htlog hlogs
  dsimp only [comparisonEnvelope] at *
  linarith

theorem auxiliaryComparisonExponent_le_envelope (B M d δ D s : ℝ)
    (hB : 1 ≤ B) (hBM : B ≤ M) (hL : 1 ≤ Real.log D) (hs : 0 < s) :
    auxiliaryComparisonExponent B d δ D s ≤ s * comparisonEnvelope M d δ (Real.log D) s := by
  have hB0 : 0 < B := by linarith
  have hb := Real.log_le_log hB0 hBM
  have hb0 := Real.log_nonneg hB
  have hnested := Real.log_le_log (by linarith : 0 < 1 + Real.log B)
    (_root_.add_le_add le_rfl hb)
  have hδ := mul_le_mul_of_nonneg_right (le_abs_self δ) (Real.log_nonneg hL)
  have hc := neg_le_abs (Real.log auxiliaryLowerConstant)
  have hnum : 2 * Real.log B + δ * Real.log (Real.log D) - Real.log auxiliaryLowerConstant ≤
      2 * Real.log M + |δ| * Real.log (Real.log D) + |Real.log auxiliaryLowerConstant| := by linarith
  have hm := mul_le_mul_of_nonneg_left hnested hs.le
  have he : s * comparisonEnvelope M d δ (Real.log D) s =
      (2 * Real.log M + |δ| * Real.log (Real.log D) + |Real.log auxiliaryLowerConstant|) +
        2 * Real.log s + s * (8 + Real.log (1 + Real.log M) + Real.log (Real.log s) +
          Real.log (Real.log D) - d * Real.log s) := by
    unfold comparisonEnvelope
    field_simp
    ring
  rw [he]
  unfold auxiliaryComparisonExponent
  nlinarith

/-- A bound at the split point controls every larger parameter. -/
theorem auxiliaryComparisonExponent_le_split_envelope (B M d δ D σ s : ℝ)
    (hB : 1 ≤ B) (hBM : B ≤ M) (hd : 1 ≤ d) (hL : 1 ≤ Real.log D)
    (hσ : Real.exp 1 ≤ σ) (hσs : σ ≤ s) :
    auxiliaryComparisonExponent B d δ D s ≤ s * comparisonEnvelope M d δ (Real.log D) σ := by
  have hs0 : 0 < s := (Real.exp_pos 1).trans_le (hσ.trans hσs)
  have h := comparisonEnvelope_antitoneOn M d δ (Real.log D) (hB.trans hBM) hd hL
    hσ (hσ.trans hσs) hσs
  exact (auxiliaryComparisonExponent_le_envelope B M d δ D s hB hBM hL hs0).trans
    (mul_le_mul_of_nonneg_left h hs0.le)

end Chen.LinearSieve
