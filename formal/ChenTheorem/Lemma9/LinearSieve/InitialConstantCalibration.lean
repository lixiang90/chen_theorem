import ChenTheorem.Lemma9.LinearSieve.BuchstabAbelian
import ChenTheorem.Lemma9.LinearSieve.BuchstabLaplaceEvaluation

open Set Filter
open scoped Topology

namespace Chen.LinearSieve

/-- Calibration of the initial value of the constructed sieve functions.
Both limits come from their convergent series; no sieve asymptotic is assumed. -/
theorem linearSieveInitialConstant_eq_two_exp_eulerMascheroni :
    linearSieveInitialConstant = 2 * Real.exp Real.eulerMascheroniConstant := by
  have h := tendsto_nhds_unique tendsto_mul_buchstabLaplace_initialConstant
    tendsto_mul_buchstabLaplace_euler
  have hm : linearSieveInitialConstant * Real.exp (-Real.eulerMascheroniConstant) = 2 := by
    have h' := (div_eq_iff linearSieveInitialConstant_pos.ne').mp h
    nlinarith [h']
  calc
    linearSieveInitialConstant = linearSieveInitialConstant *
        (Real.exp (-Real.eulerMascheroniConstant) * Real.exp Real.eulerMascheroniConstant) := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = 2 * Real.exp Real.eulerMascheroniConstant := by rw [← mul_assoc, hm]

theorem upperLinearSieveFunction_initial_calibrated (s : ℝ) (hs : 1 < s) (hs3 : s ≤ 3) :
    upperLinearSieveFunction s = 2 * Real.exp Real.eulerMascheroniConstant / s := by
  rw [upperLinearSieveFunction_initial s hs hs3,
    linearSieveInitialConstant_eq_two_exp_eulerMascheroni]

theorem lowerLinearSieveFunction_initial_calibrated (s : ℝ) (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    lowerLinearSieveFunction s =
      2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s := by
  rw [lowerLinearSieveFunction_initial s hs hs4,
    linearSieveInitialConstant_eq_two_exp_eulerMascheroni]

theorem tendsto_buchstabFunction_euler :
    Tendsto buchstabFunction atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have h := tendsto_nhds_unique tendsto_mul_buchstabLaplace_initialConstant
    tendsto_mul_buchstabLaplace_euler
  rw [← h]
  exact tendsto_buchstabFunction

end Chen.LinearSieve
