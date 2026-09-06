import ChenTheorem.Lemma9.LinearSieve.SecondInterval

open Set MeasureTheory

namespace Chen.LinearSieve

theorem integral_upperLinearSieveFunction_second (s : ℝ) (hs : 3 ≤ s) (hs5 : s ≤ 5) :
    (∫ u in (3 : ℝ)..s, upperLinearSieveFunction u) =
      linearSieveInitialConstant * (Real.log s - Real.log 3 +
        ∫ u in (3 : ℝ)..s, (1 / u) * sieveSecondIntegral u) := by
  have hc : ContinuousOn (fun u : ℝ => 1 / u) (Icc 3 s) :=
    continuousOn_const.div continuousOn_id (fun u hu => by change u ≠ 0; linarith [hu.1])
  have hinner : ContinuousOn sieveSecondIntegral (Icc 3 s) :=
    fun u hu => (continuousAt_sieveSecondIntegral u hu.1).continuousWithinAt
  have hi : IntervalIntegrable (fun u : ℝ => (1 / u) * sieveSecondIntegral u) volume 3 s :=
    (hc.mul hinner).intervalIntegrable_of_Icc hs
  have heq : (∫ u in (3 : ℝ)..s, upperLinearSieveFunction u) =
      ∫ u in (3 : ℝ)..s, linearSieveInitialConstant *
        (1 / u + (1 / u) * sieveSecondIntegral u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hs] at hu
    dsimp only
    rw [upperLinearSieveFunction_second u hu.1 (hu.2.trans hs5)]
    ring
  rw [heq, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hc.intervalIntegrable_of_Icc hs)
      hi,
    integral_one_div_of_pos (by norm_num) (by linarith), Real.log_div (by linarith) (by norm_num)]

theorem mul_lowerLinearSieveFunction_second (s : ℝ) (hs : 4 ≤ s) (hs6 : s ≤ 6) :
    s * lowerLinearSieveFunction s = linearSieveInitialConstant *
      (Real.log (s - 1) + ∫ u in (3 : ℝ)..(s - 1), (1 / u) * sieveSecondIntegral u) := by
  have h := integral_upperLinearSieveFunction_shift 4 s (by norm_num) hs
  rw [intervalIntegral.integral_comp_sub_right upperLinearSieveFunction 1] at h
  norm_num only [show (4 : ℝ) - 1 = 3 by norm_num] at h
  rw [integral_upperLinearSieveFunction_second (s - 1) (by linarith) (by linarith),
    lowerLinearSieveFunction_initial 4 (by norm_num) le_rfl] at h
  norm_num only [show (4 : ℝ) - 1 = 3 by norm_num] at h
  nlinarith

theorem lowerLinearSieveFunction_second_calibrated (s : ℝ) (hs : 4 ≤ s) (hs6 : s ≤ 6) :
    lowerLinearSieveFunction s = (2 * Real.exp Real.eulerMascheroniConstant / s) *
      (Real.log (s - 1) + ∫ u in (3 : ℝ)..(s - 1), (1 / u) * sieveSecondIntegral u) := by
  have h := mul_lowerLinearSieveFunction_second s hs hs6
  rw [linearSieveInitialConstant_eq_two_exp_eulerMascheroni] at h
  calc
    lowerLinearSieveFunction s = (2 * Real.exp Real.eulerMascheroniConstant *
        (Real.log (s - 1) + ∫ u in (3 : ℝ)..(s - 1), (1 / u) * sieveSecondIntegral u)) / s :=
      (eq_div_iff (by linarith : s ≠ 0)).mpr (by nlinarith [h])
    _ = _ := by ring

theorem lowerLinearSieveFunction_five :
    5 * lowerLinearSieveFunction 5 = 2 * Real.exp Real.eulerMascheroniConstant *
      (Real.log 4 + ∫ u in (3 : ℝ)..4, (1 / u) * sieveSecondIntegral u) := by
  have h := mul_lowerLinearSieveFunction_second 5 (by norm_num) (by norm_num)
  simpa only [linearSieveInitialConstant_eq_two_exp_eulerMascheroni,
    show (5 : ℝ) - 1 = 4 by norm_num] using h

theorem upperLinearSieveFunction_second_calibrated (s : ℝ) (hs : 3 ≤ s) (hs5 : s ≤ 5) :
    upperLinearSieveFunction s = (2 * Real.exp Real.eulerMascheroniConstant / s) *
      (1 + sieveSecondIntegral s) := by
  rw [upperLinearSieveFunction_second s hs hs5,
    linearSieveInitialConstant_eq_two_exp_eulerMascheroni]

end Chen.LinearSieve
