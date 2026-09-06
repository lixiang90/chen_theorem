import ChenTheorem.Lemma9.LinearSieve.InitialConstantCalibration

open Set MeasureTheory

namespace Chen.LinearSieve

/-- The inner integral appearing in Chen's formulas (26) and (27). -/
noncomputable def sieveSecondIntegral (s : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..(s - 1), Real.log (t - 1) / t

theorem continuousOn_sieveSecondKernel :
    ContinuousOn (fun t : ℝ => Real.log (t - 1) / t) (Ioi 1) := by
  apply ((continuousOn_id.sub continuousOn_const).log
    (fun t ht => by change t - 1 ≠ 0; linarith [show 1 < t from ht])).div continuousOn_id
  intro t ht
  change t ≠ 0
  linarith [show 1 < t from ht]

theorem continuousAt_sieveSecondIntegral (s : ℝ) (hs : 3 ≤ s) :
    ContinuousAt sieveSecondIntegral s := by
  have hi : IntervalIntegrable (fun t : ℝ => Real.log (t - 1) / t) volume 2 (s - 1) := by
    apply (continuousOn_sieveSecondKernel.mono ?_).intervalIntegrable_of_Icc (by linarith)
    intro t ht
    change 1 < t
    linarith [ht.1]
  have hc : ContinuousAt (fun t : ℝ => Real.log (t - 1) / t) (s - 1) :=
    continuousOn_sieveSecondKernel.continuousAt (Ioi_mem_nhds (by linarith))
  have hm := continuousOn_sieveSecondKernel.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi
    (s - 1) (show 1 < s - 1 by linarith)
  unfold sieveSecondIntegral
  exact ContinuousAt.comp' (f := fun v : ℝ => v - 1) (x := s)
    (intervalIntegral.integral_hasDerivAt_right hi hm hc).continuousAt
    (continuousAt_id.sub continuousAt_const)

theorem integral_lowerLinearSieveFunction_shift (a b : ℝ) (ha : 3 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, lowerLinearSieveFunction (t - 1)) =
      b * upperLinearSieveFunction b - a * upperLinearSieveFunction a := by
  have hi : ContinuousOn (fun t => lowerLinearSieveFunction (t - 1)) (Icc a b) :=
    continuousOn_lowerLinearSieveFunction.comp (continuousOn_id.sub continuousOn_const)
      (fun t ht => by change 2 ≤ t - 1; linarith [ht.1])
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (continuousOn_id.mul (continuousOn_upperLinearSieveFunction.mono
      (fun t ht => by change 1 < t; linarith [ht.1])))
    (fun t ht => hasDerivAt_mul_upperLinearSieveFunction t (by linarith [ht.1]))
    (hi.intervalIntegrable_of_Icc hab)

theorem integral_upperLinearSieveFunction_shift (a b : ℝ) (ha : 2 < a) (hab : a ≤ b) :
    (∫ t in a..b, upperLinearSieveFunction (t - 1)) =
      b * lowerLinearSieveFunction b - a * lowerLinearSieveFunction a := by
  have hi : ContinuousOn (fun t => upperLinearSieveFunction (t - 1)) (Icc a b) :=
    continuousOn_upperLinearSieveFunction.comp (continuousOn_id.sub continuousOn_const)
      (fun t ht => by change 1 < t - 1; linarith [ht.1])
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (continuousOn_id.mul (continuousOn_lowerLinearSieveFunction.mono
      (fun t ht => by change 2 ≤ t; linarith [ht.1])))
    (fun t ht => hasDerivAt_mul_lowerLinearSieveFunction t (by linarith [ht.1]))
    (hi.intervalIntegrable_of_Icc hab)

theorem mul_upperLinearSieveFunction_second (s : ℝ) (hs : 3 ≤ s) (hs5 : s ≤ 5) :
    s * upperLinearSieveFunction s = linearSieveInitialConstant * (1 + sieveSecondIntegral s) := by
  have h := integral_lowerLinearSieveFunction_shift 3 s le_rfl hs
  have heq : (∫ t in (3 : ℝ)..s, lowerLinearSieveFunction (t - 1)) =
      linearSieveInitialConstant * sieveSecondIntegral s := by
    have hi : (∫ t in (3 : ℝ)..s, lowerLinearSieveFunction (t - 1)) =
        ∫ t in (3 : ℝ)..s, linearSieveInitialConstant * (Real.log (t - 1 - 1) / (t - 1)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hs] at ht
      dsimp only
      rw [lowerLinearSieveFunction_initial (t - 1) (by linarith [ht.1]) (by linarith [ht.2])]
      ring
    rw [hi, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun t => Real.log (t - 1) / t) 1]
    norm_num only [show (3 : ℝ) - 1 = 2 by norm_num]
    rfl
  rw [heq, upperLinearSieveFunction_initial 3 (by norm_num) le_rfl] at h
  nlinarith

theorem upperLinearSieveFunction_second (s : ℝ) (hs : 3 ≤ s) (hs5 : s ≤ 5) :
    upperLinearSieveFunction s = linearSieveInitialConstant / s * (1 + sieveSecondIntegral s) := by
  have h := mul_upperLinearSieveFunction_second s hs hs5
  calc
    upperLinearSieveFunction s = linearSieveInitialConstant * (1 + sieveSecondIntegral s) / s :=
      (eq_div_iff (by linarith : s ≠ 0)).mpr (by nlinarith [h])
    _ = _ := by ring

end Chen.LinearSieve
