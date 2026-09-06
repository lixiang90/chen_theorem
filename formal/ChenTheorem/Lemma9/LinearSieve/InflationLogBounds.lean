import ChenTheorem.Lemma9.LinearSieve.GrowingSieveParameter
import ChenTheorem.Lemma9.LinearSieve.AuxiliaryInflationDerivative

namespace Chen.LinearSieve

noncomputable def inflationLogBudget (d L : ℝ) : ℝ :=
  (2 : ℝ) ^ d / (L ^ (1 / 2 : ℝ) * Real.log 3) +
    2 * d * (Real.log (1 + (3 : ℝ) ^ d) + d * Real.log (Real.log L)) / Real.log L

theorem inflation_log_small_parameter (d L a s : ℝ)
    (hd : 0 < d) (hL : 0 < L) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : 1 ≤ s) (hcut : s ≤ L ^ (1 / (2 * d))) :
    Real.log (1 + (s + a) ^ d / L) ≤ (2 : ℝ) ^ d / L ^ (1 / 2 : ℝ) := by
  have hhalf := Real.rpow_pos_of_pos hL (1 / 2 : ℝ)
  have hroot := Real.rpow_pos_of_pos hL (1 / (2 * d))
  have hpow := Real.rpow_le_rpow (show 0 ≤ s + a by linarith)
    (show s + a ≤ 2 * L ^ (1 / (2 * d)) by linarith) hd.le
  have he : (L ^ (1 / (2 * d))) ^ d = L ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul hL.le]
    congr 1
    field_simp
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hroot.le, he] at hpow
  have hsq : L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = L := by
    rw [← Real.rpow_add hL]
    norm_num
  have hfrac := div_le_div_of_nonneg_right hpow hL.le
  have heq : ((2 : ℝ) ^ d * L ^ (1 / 2 : ℝ)) / L =
      (2 : ℝ) ^ d / L ^ (1 / 2 : ℝ) := by
    apply (div_eq_div_iff hL.ne' hhalf.ne').mpr
    rw [mul_assoc, hsq]
  rw [heq] at hfrac
  have hp := Real.rpow_pos_of_pos (show 0 < s + a by linarith) d
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + (s + a) ^ d / L by positivity)
  exact (by linarith : Real.log (1 + (s + a) ^ d / L) ≤ (s + a) ^ d / L).trans hfrac

theorem inflation_log_growing_parameter (d L a s : ℝ)
    (hd : 0 < d) (hL : 1 < L) (hlog : 1 ≤ Real.log L)
    (hσ : 1 ≤ growingSieveParameter d L) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : 0 ≤ s) (hcut : s ≤ 2 * growingSieveParameter d L) :
    Real.log (1 + (s + a) ^ d / L) ≤
      Real.log (1 + (3 : ℝ) ^ d) + d * Real.log (Real.log L) := by
  have hL0 : 0 < L := by linarith
  have hl := Real.log_pos hL
  have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) d
  have hσp := growingSieveParameter_pos d L hL
  have hpow := Real.rpow_le_rpow (show 0 ≤ s + a by linarith)
    (show s + a ≤ 3 * growingSieveParameter d L by linarith) hd.le
  have he : (growingSieveParameter d L) ^ d = L * (Real.log L) ^ d := by
    rw [growingSieveParameter, Real.mul_rpow (Real.rpow_nonneg hL0.le _) hl.le,
      ← Real.rpow_mul hL0.le]
    have heq : (1 / d) * d = 1 := by field_simp
    rw [heq, Real.rpow_one]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hσp.le, he] at hpow
  have hfrac := div_le_div_of_nonneg_right hpow hL0.le
  have heq : ((3 : ℝ) ^ d * (L * Real.log L ^ d)) / L =
      (3 : ℝ) ^ d * Real.log L ^ d := by field_simp
  rw [heq] at hfrac
  have hy := Real.one_le_rpow hlog hd.le
  have hbase : 1 + (s + a) ^ d / L ≤ (1 + (3 : ℝ) ^ d) * Real.log L ^ d := by
    nlinarith
  have hb : 0 < 1 + (s + a) ^ d / L := by
    have := Real.rpow_nonneg (show 0 ≤ s + a by linarith) d
    positivity
  have h := Real.log_le_log hb hbase
  rw [Real.log_mul (by positivity : 1 + (3 : ℝ) ^ d ≠ 0)
    (Real.rpow_pos_of_pos hl d).ne', Real.log_rpow hl] at h
  exact h

/-- Two overlapping parameter ranges give a level-only budget. The upper
endpoint is twice the growing cutoff, allowing its later integer rounding. -/
theorem inflation_log_uniform_bound (d L a s : ℝ)
    (hd : 0 < d) (hL : 1 < L) (hlog : 1 ≤ Real.log L)
    (hσ : 1 ≤ growingSieveParameter d L) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : 3 ≤ s) (hcut : s ≤ 2 * growingSieveParameter d L) :
    Real.log (1 + (s + a) ^ d / L) ≤ inflationLogBudget d L * Real.log s := by
  have hL0 : 0 < L := by linarith
  have hls := Real.log_pos (show 1 < s by linarith)
  have hl3 := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
  have hhalf := Real.rpow_pos_of_pos hL0 (1 / 2 : ℝ)
  have hB : 0 ≤ Real.log (1 + (3 : ℝ) ^ d) + d * Real.log (Real.log L) := by
    have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) d
    have h1 := Real.log_nonneg (show 1 ≤ 1 + (3 : ℝ) ^ d by linarith)
    have h2 := Real.log_nonneg hlog
    positivity
  have hsmall : 0 ≤ (2 : ℝ) ^ d / (L ^ (1 / 2 : ℝ) * Real.log 3) := by positivity
  have hlarge : 0 ≤ 2 * d * (Real.log (1 + (3 : ℝ) ^ d) + d * Real.log (Real.log L)) /
      Real.log L := by positivity
  by_cases hc : s ≤ L ^ (1 / (2 * d))
  · have h := inflation_log_small_parameter d L a s hd hL0 ha ha1 (by linarith) hc
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hs
    have hm := mul_le_mul_of_nonneg_left hl hsmall
    have he : ((2 : ℝ) ^ d / (L ^ (1 / 2 : ℝ) * Real.log 3)) * Real.log 3 =
        (2 : ℝ) ^ d / L ^ (1 / 2 : ℝ) := by field_simp
    rw [he] at hm
    dsimp [inflationLogBudget]
    nlinarith [mul_nonneg hlarge hls.le]
  · have h := inflation_log_growing_parameter d L a s hd hL hlog hσ ha ha1 (by linarith) hcut
    have hl := Real.log_le_log (Real.rpow_pos_of_pos hL0 (1 / (2 * d))) (le_of_not_ge hc)
    rw [Real.log_rpow hL0] at hl
    have hd2 : 0 < 2 * d := by positivity
    have hlogL := Real.log_pos hL
    have hr : Real.log L ≤ 2 * d * Real.log s := by
      have he : (1 / (2 * d)) * Real.log L = Real.log L / (2 * d) := by ring
      rw [he] at hl
      have h := (div_le_iff₀ hd2).mp hl
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hr hB
    have hb : Real.log (1 + (3 : ℝ) ^ d) + d * Real.log (Real.log L) ≤
        (2 * d * (Real.log (1 + (3 : ℝ) ^ d) + d * Real.log (Real.log L)) / Real.log L) *
          Real.log s := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlogL]
      nlinarith
    dsimp [inflationLogBudget]
    nlinarith [mul_nonneg hsmall hls.le]

end Chen.LinearSieve
