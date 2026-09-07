import Submission.ChenTheorem.Lemma9.LinearSieve.RosserGrowingTail

set_option autoImplicit true
namespace Chen.LinearSieve

/-- The exponential series at `N` gives the factorial bound with the
correct coefficient of `N log N`, without a Stirling asymptotic. -/
theorem pow_div_factorial_le_exponential (x : ℝ) (hx : 0 < x) (N : ℕ) (hN : 0 < N) :
    x ^ N / N.factorial ≤ Real.exp ((N : ℝ) * (1 + Real.log x - Real.log N)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Real.pow_div_factorial_le_exp (N : ℝ) hNR.le N
  calc
    _ = (x / N) ^ N * ((N : ℝ) ^ N / N.factorial) := by rw [div_pow]; field_simp
    _ ≤ (x / N) ^ N * Real.exp N := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (div_pos hx hNR),
        Real.log_div hx.ne' hNR.ne', ← Real.exp_add]
      congr 1
      ring

theorem factorial_log_tail_le_exponential (B : ℝ) (hB : 1 < B) (N : ℕ) (hN : 0 < N) :
    B ^ 2 * (Real.log B ^ N / N.factorial) ≤
      Real.exp (2 * Real.log B + (N : ℝ) *
        (1 + Real.log (Real.log B) - Real.log N)) := by
  have h := mul_le_mul_of_nonneg_left
    (pow_div_factorial_le_exponential (Real.log B) (Real.log_pos hB) N hN) (sq_nonneg B)
  have he : B ^ 2 = Real.exp (2 * Real.log B) := by
    symm
    simpa using Real.exp_nat_mul (Real.log B) 2 |>.trans
      (by rw [Real.exp_log (by linarith : 0 < B)])
  rw [he, ← Real.exp_add] at h
  rwa [he]

/-- Remove the integer-depth rounding while retaining the sharp
`-s log s` term. The loss from the three missing depths is explicit. -/
theorem factorial_log_tail_le_parameter_exponential (B s : ℝ) (hB : 1 < B) (hs : 6 ≤ s)
    (N : ℕ) (hNlo : s - 3 ≤ (N : ℝ)) (hNhi : (N : ℝ) ≤ s) :
    B ^ 2 * (Real.log B ^ N / N.factorial) ≤
      Real.exp (2 * Real.log B + 3 * Real.log s +
        s * (2 + Real.log (1 + Real.log B) - Real.log s)) := by
  have hs0 : 0 < s := by linarith
  have hNR : (0 : ℝ) < N := by linarith
  have hN : 0 < N := by exact_mod_cast hNR
  have hb0 := Real.log_pos hB
  have hl := Real.log_le_log hb0 (show Real.log B ≤ 1 + Real.log B by linarith)
  have hlplus : 0 ≤ Real.log (1 + Real.log B) := Real.log_nonneg (by linarith)
  have hlogN := Real.log_le_log (by positivity : 0 < s / 2)
    (show s / 2 ≤ (N : ℝ) by linarith)
  rw [Real.log_div hs0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlogN
  have hlogS : 0 ≤ Real.log s - Real.log 2 := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ s)
    linarith
  have hlinear : (N : ℝ) * (1 + Real.log (Real.log B)) ≤
      s * (1 + Real.log (1 + Real.log B)) := by
    calc
      _ ≤ (N : ℝ) * (1 + Real.log (1 + Real.log B)) :=
        mul_le_mul_of_nonneg_left (_root_.add_le_add le_rfl hl) hNR.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hNhi (by linarith)
  have hquad := _root_.mul_le_mul hNlo hlogN hlogS hNR.le
  have hl2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hl2one : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hsmall := mul_nonneg hs0.le (sub_nonneg.mpr hl2one)
  apply (factorial_log_tail_le_exponential B hB N hN).trans
  apply Real.exp_le_exp.mpr
  nlinarith

end Chen.LinearSieve
