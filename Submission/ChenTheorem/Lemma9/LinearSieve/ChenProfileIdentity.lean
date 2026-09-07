import Submission.ChenTheorem.Lemma9.LinearSieve.WeightedProfileIntegral

set_option autoImplicit true
open Set MeasureTheory

namespace Chen.LinearSieve

theorem exp_neg_euler_mul_initialConstant :
    Real.exp (-Real.eulerMascheroniConstant) * linearSieveInitialConstant = 2 := by
  rw [linearSieveInitialConstant_eq_two_exp_eulerMascheroni, mul_left_comm,
    ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

theorem equation27Integral_eq_sieveSecondIntegral :
    equation27Integral = (∫ u : ℝ in 3..4, (1 / u) * sieveSecondIntegral u) -
      (1 / 4) * ∫ α : ℝ in (1 / 10)..(1 / 5),
        (1 / (α * (1 / 2 - α))) * sieveSecondIntegral (5 - 10 * α) := rfl

/-- The calibrated continuous main terms combine to exactly Chen's equation (26).
The remaining discrete weighted-sieve argument must approach this value. -/
theorem chen_continuous_sieve_profile_identity :
    20 * Real.exp (-Real.eulerMascheroniConstant) * lowerLinearSieveFunction 5 -
      10 * Real.exp (-Real.eulerMascheroniConstant) *
        (∫ α : ℝ in (1 / 10)..(1 / 3), upperLinearSieveFunction (5 - 10 * α) / α) =
      8 * (Real.log 4 - Real.log 8 / 2 + equation27Integral) := by
  have h5 : lowerLinearSieveFunction 5 = linearSieveInitialConstant / 5 *
      (Real.log 4 + ∫ u : ℝ in 3..4, (1 / u) * sieveSecondIntegral u) := by
    have h := mul_lowerLinearSieveFunction_second 5 (by norm_num) (by norm_num)
    norm_num only [show (5 : ℝ) - 1 = 4 by norm_num] at h
    nlinarith
  rw [h5, integral_weightedUpperSieve, equation27Integral_eq_sieveSecondIntegral]
  calc
    _ = (Real.exp (-Real.eulerMascheroniConstant) * linearSieveInitialConstant) *
        (4 * (Real.log 4 + ∫ u : ℝ in 3..4, (1 / u) * sieveSecondIntegral u) -
          2 * Real.log 8 - ∫ α : ℝ in (1 / 10)..(1 / 5),
            (1 / (α * (1 / 2 - α))) * sieveSecondIntegral (5 - 10 * α)) := by ring
    _ = _ := by rw [exp_neg_euler_mul_initialConstant]; ring

end Chen.LinearSieve
