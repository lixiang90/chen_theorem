import Submission.ChenTheorem.Lemma9.LinearSieve.UpperPrimeWeight

set_option autoImplicit true
open Set MeasureTheory

namespace Chen.LinearSieve

/-- The logarithmic change of variables for an arbitrary weight on a positive
power interval. It applies equally to the two prime-sieve families. -/
theorem integral_normalizedLog_weight (X c d : ℝ) (hX : 1 < X) (hc : 0 < c)
    (hcd : c ≤ d) (f : ℝ → ℝ) :
    (∫ t in Ioc (X ^ c) (X ^ d), f (normalizedLog X t) / (t * Real.log t)) =
      ∫ α in c..d, f α / α := by
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX
  have hab : X ^ c ≤ X ^ d := Real.rpow_le_rpow_of_exponent_le hX.le hcd
  have ha : 1 < X ^ c := Real.one_lt_rpow hX hc
  have hd : ∀ t ∈ uIcc (X ^ c) (X ^ d),
      HasDerivAt (normalizedLog X) (1 / (t * Real.log X)) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact hasDerivAt_normalizedLog_pos X t ((Real.rpow_pos_of_pos hX0 _).trans_le ht.1)
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := normalizedLog X) (f' := fun t => 1 / (t * Real.log X)) (g := fun α => f α / α)
    (HasDerivAt.continuousOn hd) (fun t ht => hd t (Ioo_subset_Icc_self ht))
    (fun t ht => by
      have ht0 : 0 < t := by
        rw [min_eq_left hab] at ht
        exact (Real.rpow_pos_of_pos hX0 _).trans ht.1
      exact (div_pos (by norm_num) (mul_pos ht0 hL)).le)
  rw [normalizedLog_rpow X c hX, normalizedLog_rpow X d hX] at h
  rw [← intervalIntegral.integral_of_le hab, ← h]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  have ht1 : 1 < t := ha.trans_le ht.1
  have ht0 : t ≠ 0 := ne_of_gt (by linarith : 0 < t)
  have hlt : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
  dsimp only [Function.comp_def]
  unfold normalizedLog
  field_simp

theorem integral_upperSievePrimeWeight (a X : ℝ) (hX : 1 < X) :
    (∫ t in Ioc (X ^ (1 / 10 : ℝ)) (X ^ (1 / 3 : ℝ)), upperSievePrimeWeight a X t / (t * Real.log t)) =
      ∫ α : ℝ in (1 / 10)..(1 / 3), upperLinearSieveFunction (10 * a - 10 * α) / α := by
  exact integral_normalizedLog_weight X (1 / 10) (1 / 3) hX (by norm_num) (by norm_num)
    (fun α => upperLinearSieveFunction (10 * a - 10 * α))

end Chen.LinearSieve
