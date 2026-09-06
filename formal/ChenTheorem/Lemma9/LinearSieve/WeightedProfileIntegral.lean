import ChenTheorem.Lemma9.LinearSieve.LowerSecondInterval
import ChenTheorem.Main.NumericalBounds

open Set MeasureTheory

namespace Chen.LinearSieve

theorem continuousOn_weightedSieveBase :
    ContinuousOn (fun α : ℝ => 1 / (α * (5 - 10 * α))) (Icc (1 / 10) (1 / 3)) := by
  apply continuousOn_const.div (continuousOn_id.mul
    (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)))
  intro α hα
  change α * (5 - 10 * α) ≠ 0
  exact mul_ne_zero (by linarith [hα.1]) (by linarith [hα.2])

theorem integral_weightedSieveBase :
    (∫ α : ℝ in (1 / 10)..(1 / 3), 1 / (α * (5 - 10 * α))) = Real.log 8 / 5 := by
  have hd : ∀ α ∈ uIcc (1 / 10 : ℝ) (1 / 3),
      HasDerivAt (fun α : ℝ => (Real.log α - Real.log (1 / 2 - α)) / 5)
        (1 / (α * (5 - 10 * α))) α := by
    intro α hα
    rw [uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)] at hα
    have hα0 : α ≠ 0 := by linarith [hα.1]
    have hαh : 1 / 2 - α ≠ 0 := by linarith [hα.2]
    have hα2 : 1 - α * 2 ≠ 0 := by linarith [hα.2]
    have hα5 : 5 - α * 10 ≠ 0 := by linarith [hα.2]
    have h := ((Real.hasDerivAt_log hα0).sub
      (((hasDerivAt_id α).const_sub (1 / 2)).log hαh)).div_const 5
    apply h.congr_deriv
    dsimp only [id_eq]
    field_simp [hα0, hαh, hα2, hα5]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (continuousOn_weightedSieveBase.intervalIntegrable_of_Icc (by norm_num))]
  rw [← Real.log_div (by norm_num : (1 / 3 : ℝ) ≠ 0) (by norm_num),
    ← Real.log_div (by norm_num : (1 / 10 : ℝ) ≠ 0) (by norm_num)]
  norm_num only [show (1 / 3 : ℝ) / (1 / 2 - 1 / 3) = 2 by norm_num,
    show (1 / 10 : ℝ) / (1 / 2 - 1 / 10) = 1 / 4 by norm_num]
  rw [← sub_div, ← Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by norm_num)]
  norm_num

theorem continuousOn_weightedUpperSieve :
    ContinuousOn (fun α : ℝ => upperLinearSieveFunction (5 - 10 * α) / α)
      (Icc (1 / 10) (1 / 3)) := by
  apply (continuousOn_upperLinearSieveFunction.comp
    (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
    (fun α hα => by change 1 < 5 - 10 * α; linarith [hα.2])).div continuousOn_id
  intro α hα
  change α ≠ 0
  linarith [hα.1]

theorem continuousOn_weightedSieveCorrection :
    ContinuousOn (fun α : ℝ => (1 / (α * (1 / 2 - α))) * sieveSecondIntegral (5 - 10 * α))
      (Icc (1 / 10) (1 / 5)) := by
  have hinner : ContinuousOn (fun α : ℝ => sieveSecondIntegral (5 - 10 * α))
      (Icc (1 / 10) (1 / 5)) := by
    intro α hα
    apply ContinuousAt.continuousWithinAt
    exact ContinuousAt.comp' (f := fun α : ℝ => 5 - 10 * α) (x := α)
      (continuousAt_sieveSecondIntegral _ (by linarith [hα.2]))
      (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
  apply (continuousOn_const.div (continuousOn_id.mul
    (continuousOn_const.sub continuousOn_id)) (fun α hα => by
      change α * (1 / 2 - α) ≠ 0
      exact mul_ne_zero (by linarith [hα.1]) (by linarith [hα.2]))).mul
    hinner

theorem integral_weightedUpperSieve :
    (∫ α : ℝ in (1 / 10)..(1 / 3), upperLinearSieveFunction (5 - 10 * α) / α) =
      linearSieveInitialConstant * Real.log 8 / 5 + linearSieveInitialConstant / 10 *
        ∫ α : ℝ in (1 / 10)..(1 / 5),
          (1 / (α * (1 / 2 - α))) * sieveSecondIntegral (5 - 10 * α) := by
  have hsub1 : Icc (1 / 10 : ℝ) (1 / 5) ⊆ Icc (1 / 10) (1 / 3) := by
    intro α hα
    exact ⟨hα.1, by linarith [hα.2]⟩
  have hsub2 : Icc (1 / 5 : ℝ) (1 / 3) ⊆ Icc (1 / 10) (1 / 3) := by
    intro α hα
    exact ⟨by linarith [hα.1], hα.2⟩
  have hsmall : (∫ α : ℝ in (1 / 10)..(1 / 5), upperLinearSieveFunction (5 - 10 * α) / α) =
      linearSieveInitialConstant * (∫ α : ℝ in (1 / 10)..(1 / 5), 1 / (α * (5 - 10 * α))) +
        linearSieveInitialConstant / 10 * ∫ α : ℝ in (1 / 10)..(1 / 5),
          (1 / (α * (1 / 2 - α))) * sieveSecondIntegral (5 - 10 * α) := by
    have heq : (∫ α : ℝ in (1 / 10)..(1 / 5), upperLinearSieveFunction (5 - 10 * α) / α) =
        ∫ α : ℝ in (1 / 10)..(1 / 5),
          linearSieveInitialConstant * (1 / (α * (5 - 10 * α))) +
          linearSieveInitialConstant / 10 * ((1 / (α * (1 / 2 - α))) * sieveSecondIntegral (5 - 10 * α)) := by
      apply intervalIntegral.integral_congr
      intro α hα
      rw [uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 5)] at hα
      dsimp only
      rw [upperLinearSieveFunction_second (5 - 10 * α) (by linarith [hα.2]) (by linarith [hα.1])]
      have hα0 : α ≠ 0 := by linarith [hα.1]
      have hαh : 1 / 2 - α ≠ 0 := by linarith [hα.2]
      have hα5 : 5 - 10 * α ≠ 0 := by linarith [hα.2]
      have hα2 : 1 - α * 2 ≠ 0 := by linarith [hα.2]
      field_simp [hα0, hαh, hα5, hα2]
      ring
    rw [heq, intervalIntegral.integral_add
      (((continuousOn_weightedSieveBase.mono hsub1).intervalIntegrable_of_Icc (by norm_num)).const_mul _)
      ((continuousOn_weightedSieveCorrection.intervalIntegrable_of_Icc (by norm_num)).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hbig : (∫ α : ℝ in (1 / 5)..(1 / 3), upperLinearSieveFunction (5 - 10 * α) / α) =
      linearSieveInitialConstant * ∫ α : ℝ in (1 / 5)..(1 / 3), 1 / (α * (5 - 10 * α)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro α hα
    rw [uIcc_of_le (by norm_num : (1 / 5 : ℝ) ≤ 1 / 3)] at hα
    dsimp only
    rw [upperLinearSieveFunction_initial (5 - 10 * α) (by linarith [hα.2]) (by linarith [hα.1])]
    field_simp
  have hjoin := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((continuousOn_weightedUpperSieve.mono hsub1).intervalIntegrable_of_Icc (by norm_num))
    ((continuousOn_weightedUpperSieve.mono hsub2).intervalIntegrable_of_Icc (by norm_num))
  have hbase := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((continuousOn_weightedSieveBase.mono hsub1).intervalIntegrable_of_Icc (by norm_num))
    ((continuousOn_weightedSieveBase.mono hsub2).intervalIntegrable_of_Icc (by norm_num))
  rw [hsmall, hbig] at hjoin
  rw [integral_weightedSieveBase] at hbase
  linear_combination -hjoin + linearSieveInitialConstant * hbase

end Chen.LinearSieve
