import ChenTheorem.Analysis.BlaschkeFactor

open Set Metric
open scoped ComplexConjugate

namespace Chen

theorem logDeriv_blaschkeFactor {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 R) (hzw : z ≠ w) :
    logDeriv (blaschkeFactor R w) z =
      1 / (z - w) + conj w / ((R : ℂ) ^ 2 - conj w * z) := by
  have hR : (R : ℂ) ≠ 0 := by exact_mod_cast (pos_of_mem_ball hw).ne'
  have hn : (R : ℂ) * (z - w) ≠ 0 := mul_ne_zero hR (sub_ne_zero.mpr hzw)
  have hd := blaschke_denominator_ne_zero hw hz
  unfold blaschkeFactor
  rw [logDeriv_div z hn hd (by fun_prop) (by fun_prop), logDeriv_const_mul z (R : ℂ) hR]
  simp only [logDeriv_apply, deriv_sub_const, deriv_id'', deriv_const_sub, deriv_const_mul_id]
  ring

/-- Each reflected-zero term in the Blaschke logarithmic derivative is
bounded by `4/R` on the three-quarter disk. -/
theorem norm_blaschke_logDeriv_correction_le {R : ℝ} {w z : ℂ}
    (hw : w ∈ ball 0 R) (hz : ‖z‖ ≤ 3 * R / 4) :
    ‖conj w / ((R : ℂ) ^ 2 - conj w * z)‖ ≤ 4 / R := by
  have hwR : ‖w‖ < R := by simpa using hw
  have hR : 0 < R := pos_of_mem_ball hw
  have hmul : ‖w‖ * ‖z‖ ≤ 3 * R ^ 2 / 4 := by
    have h := mul_le_mul hwR.le hz (norm_nonneg z) hR.le
    nlinarith
  have hden := norm_sub_norm_le ((R : ℂ) ^ 2) (conj w * z)
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
    norm_mul, Complex.norm_conj] at hden
  have hdenlower : R ^ 2 / 4 ≤ ‖(R : ℂ) ^ 2 - conj w * z‖ := by linarith
  have hdenpos : 0 < ‖(R : ℂ) ^ 2 - conj w * z‖ := by nlinarith
  rw [norm_div, Complex.norm_conj]
  apply (div_le_div_iff₀ hdenpos hR).mpr
  nlinarith

end Chen
