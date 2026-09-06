import ChenTheorem.Lemma9.LinearSieve.BuchstabLaplace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Set Filter MeasureTheory
open scoped Topology

namespace Chen.LinearSieve

/-- Extension by zero used only to put all dilated Laplace integrals on one domain. -/
noncomputable def buchstabExtended (s : ℝ) : ℝ := (Ioi (1 : ℝ)).indicator buchstabFunction s

theorem buchstabExtended_eq (s : ℝ) (hs : 1 < s) :
    buchstabExtended s = buchstabFunction s := indicator_of_mem hs _

theorem measurable_buchstabExtended : Measurable buchstabExtended := by
  have hc := continuousOn_buchstabFunction.comp_continuous
    (continuous_id.max continuous_const) (fun s => show 1 ≤ max s 1 from le_max_right _ _)
  have heq : buchstabExtended = (Ioi (1 : ℝ)).indicator (fun s => buchstabFunction (max s 1)) := by
    funext s
    by_cases hs : 1 < s
    · simp [buchstabExtended, hs, max_eq_left hs.le]
    · simp [buchstabExtended, hs]
  rw [heq]
  exact hc.measurable.indicator measurableSet_Ioi

theorem buchstabExtended_bounds (s : ℝ) :
    0 ≤ buchstabExtended s ∧ buchstabExtended s ≤ 2 := by
  by_cases hs : 1 < s
  · rw [buchstabExtended_eq s hs]
    exact buchstabFunction_bounds s hs.le
  · simp [buchstabExtended, hs]

theorem tendsto_buchstabExtended :
    Tendsto buchstabExtended atTop (𝓝 (2 / linearSieveInitialConstant)) := by
  apply tendsto_buchstabFunction.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
  exact (buchstabExtended_eq s hs).symm

theorem integral_buchstabExtended (t : ℝ) :
    (∫ s in Ioi (0 : ℝ), buchstabExtended s * Real.exp (-t * s)) = buchstabLaplace t := by
  have heq : (fun s => buchstabExtended s * Real.exp (-t * s)) =
      (Ioi (1 : ℝ)).indicator (fun s => buchstabFunction s * Real.exp (-t * s)) := by
    funext s
    by_cases hs : 1 < s <;> simp [buchstabExtended, hs]
  rw [heq, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
  rfl

theorem mul_buchstabLaplace_eq_dilated (t : ℝ) (ht : 0 < t) :
    t * buchstabLaplace t =
      ∫ u in Ioi (0 : ℝ), buchstabExtended (u / t) * Real.exp (-u) := by
  have h := integral_comp_mul_left_Ioi
    (fun u => buchstabExtended (u / t) * Real.exp (-u)) 0 ht
  have heq : (fun s => buchstabExtended (t * s / t) * Real.exp (-(t * s))) =
      (fun s => buchstabExtended s * Real.exp (-t * s)) := by
    funext s
    rw [mul_div_cancel_left₀ s ht.ne', neg_mul]
  simp only [heq, mul_zero, smul_eq_mul, integral_buchstabExtended] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]

theorem tendsto_mul_buchstabLaplace_initialConstant :
    Tendsto (fun t => t * buchstabLaplace t) (𝓝[>] 0)
      (𝓝 (2 / linearSieveInitialConstant)) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ))
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun t u : ℝ => buchstabExtended (u / t) * Real.exp (-u))
    (f := fun u => (2 / linearSieveInitialConstant) * Real.exp (-u))
    (fun u : ℝ => 2 * Real.exp (-u)) ?_ ?_ ((integrableOn_exp_neg_Ioi 0).const_mul 2) ?_
  · have hint : (∫ u in Ioi (0 : ℝ), (2 / linearSieveInitialConstant) * Real.exp (-u)) =
        2 / linearSieveInitialConstant := by
      rw [integral_const_mul]
      have he : (∫ u in Ioi (0 : ℝ), Real.exp (-u)) = 1 := by
        simpa using integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
      rw [he, mul_one]
    rw [hint] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (mul_buchstabLaplace_eq_dilated t ht).symm
  · exact Eventually.of_forall (fun t =>
      ((measurable_buchstabExtended.comp (measurable_id.div_const t)).mul
        (Real.measurable_exp.comp measurable_neg)).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro t
    exact Eventually.of_forall (fun u => by
      have hb := buchstabExtended_bounds (u / t)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_right hb.2 (Real.exp_pos _).le)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hd : Tendsto (fun t : ℝ => u / t) (𝓝[>] 0) atTop := by
      simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hu
    exact (tendsto_buchstabExtended.comp hd).mul_const (Real.exp (-u))

end Chen.LinearSieve
