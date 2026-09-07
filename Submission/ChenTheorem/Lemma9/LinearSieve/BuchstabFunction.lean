import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousFunctions
import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousUpperSmooth
import Mathlib.Topology.Piecewise

set_option autoImplicit true

open Set Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The Buchstab function obtained from the two constructed sieve functions. -/
noncomputable def buchstabFunction (s : ℝ) : ℝ :=
  if s ≤ 2 then 1 / s
  else (upperLinearSieveFunction s + lowerLinearSieveFunction s) / linearSieveInitialConstant

theorem linearSieveInitialConstant_pos : 0 < linearSieveInitialConstant :=
  lt_of_lt_of_le (by norm_num) linearSieveInitialConstant_ge_three

theorem buchstabFunction_initial (s : ℝ) (hs : s ≤ 2) :
    buchstabFunction s = 1 / s := by
  simp [buchstabFunction, hs]

theorem buchstabFunction_eq_sieve (s : ℝ) (hs : 2 ≤ s) :
    buchstabFunction s =
      (upperLinearSieveFunction s + lowerLinearSieveFunction s) /
        linearSieveInitialConstant := by
  rcases hs.eq_or_lt with rfl | hs
  · rw [buchstabFunction_initial 2 le_rfl,
      upperLinearSieveFunction_initial 2 (by norm_num) (by norm_num),
      lowerLinearSieveFunction_two]
    field_simp [ne_of_gt linearSieveInitialConstant_pos]
    ring
  · simp [buchstabFunction, not_le.mpr hs]

theorem continuousOn_buchstabFunction : ContinuousOn buchstabFunction (Ici 1) := by
  unfold buchstabFunction
  apply ContinuousOn.if
  · intro s hs
    have hs2 : s = 2 := by
      simpa only [show {a : ℝ | a ≤ 2} = Iic 2 from rfl,
        frontier_Iic, mem_singleton_iff] using hs.2
    subst s
    simpa only [buchstabFunction_initial 2 le_rfl] using buchstabFunction_eq_sieve 2 le_rfl
  · apply continuousOn_const.div continuousOn_id
    intro s hs
    have : 1 ≤ s := hs.1
    change s ≠ 0
    linarith
  · apply ((continuousOn_upperLinearSieveFunction.mono ?_).add
      (continuousOn_lowerLinearSieveFunction.mono ?_)).div_const
    · intro s hs
      have : 2 ≤ s := by
        simpa only [show {a : ℝ | ¬a ≤ 2} = Ioi 2 from by ext a; simp,
          closure_Ioi, mem_Ici] using hs.2
      change 1 < s
      linarith
    · intro s hs
      simpa only [show {a : ℝ | ¬a ≤ 2} = Ioi 2 from by ext a; simp,
        closure_Ioi] using hs.2

theorem buchstabFunction_bounds (s : ℝ) (hs : 1 ≤ s) :
    0 ≤ buchstabFunction s ∧ buchstabFunction s ≤ 2 := by
  by_cases hs2 : s ≤ 2
  · rw [buchstabFunction_initial s hs2]
    constructor
    · positivity
    · exact (div_le_one (by linarith : 0 < s)).mpr hs |>.trans (by norm_num)
  · have hs2' : 2 ≤ s := (not_le.mp hs2).le
    rw [buchstabFunction_eq_sieve s hs2']
    have hF := upperLinearSieveFunction_ge_one s (by linarith)
    have hf := lowerLinearSieveFunction_bounds s hs2'
    have hU := (upperContinuousError_bounds s (by linarith)).2
    rw [min_eq_right hs2'] at hU
    constructor
    · exact div_nonneg (by linarith) linearSieveInitialConstant_pos.le
    · apply (div_le_iff₀ linearSieveInitialConstant_pos).mpr
      dsimp [upperLinearSieveFunction] at *
      linarith [linearSieveInitialConstant_ge_three]

theorem tendsto_buchstabFunction :
    Tendsto buchstabFunction atTop (𝓝 (2 / linearSieveInitialConstant)) := by
  have h := (tendsto_upperLinearSieveFunction_one.add
    tendsto_lowerLinearSieveFunction_one).div_const linearSieveInitialConstant
  norm_num only [show (1 : ℝ) + 1 = 2 by norm_num] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
  exact (buchstabFunction_eq_sieve s hs).symm

theorem hasDerivAt_mul_upperLinearSieveFunction_all (s : ℝ) (hs : 1 < s) :
    HasDerivAt (fun t => t * upperLinearSieveFunction t)
      (1 - lowerContinuousError (max (s - 1) 2)) s := by
  convert! (hasDerivAt_id s).add (hasDerivAt_mul_upperContinuousError_all s hs) using 1
  · funext t
    dsimp [upperLinearSieveFunction]
    ring

theorem hasDerivAt_mul_buchstabFunction (s : ℝ) (hs : 2 < s) :
    HasDerivAt (fun t => t * buchstabFunction t) (buchstabFunction (s - 1)) s := by
  have h := ((hasDerivAt_mul_upperLinearSieveFunction_all s (by linarith)).add
    (hasDerivAt_mul_lowerLinearSieveFunction s hs)).div_const linearSieveInitialConstant
  have heq : (fun t => t * buchstabFunction t) =ᶠ[𝓝 s]
      (fun t => (t * upperLinearSieveFunction t + t * lowerLinearSieveFunction t) /
        linearSieveInitialConstant) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    rw [buchstabFunction_eq_sieve t ht.le]
    ring
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  by_cases hs3 : s ≤ 3
  · rw [max_eq_right (by linarith), lowerContinuousError_two,
      upperLinearSieveFunction_initial (s - 1) (by linarith) (by linarith),
      buchstabFunction_initial (s - 1) (by linarith)]
    field_simp [ne_of_gt linearSieveInitialConstant_pos]
    ring
  · rw [max_eq_left (by linarith), buchstabFunction_eq_sieve (s - 1) (by linarith)]
    dsimp [lowerLinearSieveFunction]
    ring

theorem buchstabFunction_integral_equation (s : ℝ) (hs : 2 ≤ s) :
    s * buchstabFunction s = 1 + ∫ t in (2 : ℝ)..s, buchstabFunction (t - 1) := by
  have hc : ContinuousOn (fun t => buchstabFunction (t - 1)) (Icc 2 s) :=
    continuousOn_buchstabFunction.comp (continuousOn_id.sub continuousOn_const)
      (fun t ht => by change 1 ≤ t - 1; linarith [ht.1])
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs
    (continuousOn_id.mul (continuousOn_buchstabFunction.mono
      (fun t ht => by change 1 ≤ t; linarith [ht.1])))
    (fun t ht => hasDerivAt_mul_buchstabFunction t ht.1)
    (hc.intervalIntegrable_of_Icc hs)
  simp only [Pi.mul_apply, id_eq, buchstabFunction_initial 2 le_rfl] at h
  linarith

end Chen.LinearSieve
