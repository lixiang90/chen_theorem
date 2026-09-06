import ChenTheorem.Lemma9.LinearSieve.ContinuousEndpoint

open Set Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The upper linear-sieve function constructed from its convergent error series. -/
noncomputable def upperLinearSieveFunction (s : ℝ) : ℝ := 1 + upperContinuousError s

/-- The lower linear-sieve function on its analytic domain `s ≥ 2`. -/
noncomputable def lowerLinearSieveFunction (s : ℝ) : ℝ := 1 - lowerContinuousError s

theorem upperLinearSieveFunction_ge_one (s : ℝ) (hs : 1 < s) :
    1 ≤ upperLinearSieveFunction s := by
  have h := (upperContinuousError_bounds s hs).1
  dsimp [upperLinearSieveFunction]
  linarith

theorem lowerLinearSieveFunction_bounds (s : ℝ) (hs : 2 ≤ s) :
    0 ≤ lowerLinearSieveFunction s ∧ lowerLinearSieveFunction s ≤ 1 := by
  have h := lowerContinuousError_bounds s hs
  dsimp [lowerLinearSieveFunction]
  constructor <;> linarith [h.1, h.2]

theorem upperLinearSieveFunction_initial (s : ℝ) (hs : 1 < s) (hs3 : s ≤ 3) :
    upperLinearSieveFunction s = linearSieveInitialConstant / s := by
  unfold upperLinearSieveFunction
  rw [upperContinuousError_initial s hs hs3]
  ring

theorem lowerLinearSieveFunction_initial (s : ℝ) (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    lowerLinearSieveFunction s = linearSieveInitialConstant * Real.log (s - 1) / s := by
  unfold lowerLinearSieveFunction
  rw [lowerContinuousError_initial s hs hs4]
  ring

theorem lowerLinearSieveFunction_two : lowerLinearSieveFunction 2 = 0 := by
  simp [lowerLinearSieveFunction, lowerContinuousError_two]

theorem continuousOn_upperLinearSieveFunction :
    ContinuousOn upperLinearSieveFunction (Ioi 1) :=
  continuousOn_const.add continuousOn_upperContinuousError

theorem continuousOn_lowerLinearSieveFunction :
    ContinuousOn lowerLinearSieveFunction (Ici 2) :=
  continuousOn_const.sub continuousOn_lowerContinuousError

theorem tendsto_upperLinearSieveFunction_one :
    Tendsto upperLinearSieveFunction atTop (𝓝 1) := by
  unfold upperLinearSieveFunction
  simpa only [add_zero] using tendsto_const_nhds.add tendsto_upperContinuousError_zero

theorem tendsto_lowerLinearSieveFunction_one :
    Tendsto lowerLinearSieveFunction atTop (𝓝 1) := by
  unfold lowerLinearSieveFunction
  simpa only [sub_zero] using tendsto_const_nhds.sub tendsto_lowerContinuousError_zero

theorem hasDerivAt_mul_upperLinearSieveFunction (s : ℝ) (hs : 3 < s) :
    HasDerivAt (fun t => t * upperLinearSieveFunction t) (lowerLinearSieveFunction (s - 1)) s := by
  convert! (hasDerivAt_id s).add (hasDerivAt_mul_upperContinuousError s hs) using 1
  funext t
  dsimp [upperLinearSieveFunction]
  ring

theorem hasDerivAt_mul_lowerLinearSieveFunction (s : ℝ) (hs : 2 < s) :
    HasDerivAt (fun t => t * lowerLinearSieveFunction t) (upperLinearSieveFunction (s - 1)) s := by
  convert! (hasDerivAt_id s).sub (hasDerivAt_mul_lowerContinuousError s hs) using 1
  · funext t
    dsimp [lowerLinearSieveFunction]
    ring
  · dsimp [upperLinearSieveFunction]
    ring

end Chen.LinearSieve
