import ChenTheorem.Lemma9.LinearSieve.BuchstabLaplaceEquation
import ChenTheorem.Lemma9.LinearSieve.ExponentialIntegral

open Set Filter MeasureTheory
open scoped Topology

namespace Chen.LinearSieve

theorem tendsto_buchstabLaplace_zero : Tendsto buchstabLaplace atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => 2 / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (2 : ℝ)
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (buchstabLaplace_bounds t ht).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    apply (buchstabLaplace_bounds t ht).2.trans
    apply div_le_div_of_nonneg_right _ ht.le
    have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith

theorem hasDerivAt_log_buchstabLaplace (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t => Real.log (1 + buchstabLaplace t)) (-Real.exp (-t) / t) t := by
  have hp : 0 < 1 + buchstabLaplace t := by linarith [(buchstabLaplace_bounds t ht).1]
  have h := ((hasDerivAt_buchstabLaplace_equation t ht).const_add 1).log hp.ne'
  simpa only [mul_div_cancel_right₀ _ hp.ne'] using h

theorem log_buchstabLaplace_eq_exponentialIntegral (t : ℝ) (ht : 0 < t) :
    Real.log (1 + buchstabLaplace t) = exponentialIntegral t := by
  have hlim : Tendsto (fun t => Real.log (1 + buchstabLaplace t)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds.add tendsto_buchstabLaplace_zero).log (by norm_num : (1 : ℝ) + 0 ≠ 0)
    simpa only [add_zero, Real.log_one] using h
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u hu => hasDerivAt_log_buchstabLaplace u (lt_of_lt_of_le ht hu))
    (by simpa only [Pi.neg_def, neg_div] using (integrableOn_exponentialIntegral t ht).neg) hlim
  simp only [neg_div, integral_neg, zero_sub] at h
  unfold exponentialIntegral
  linarith

theorem buchstabLaplace_eq_exp_exponentialIntegral (t : ℝ) (ht : 0 < t) :
    buchstabLaplace t = Real.exp (exponentialIntegral t) - 1 := by
  have hp : 0 < 1 + buchstabLaplace t := by linarith [(buchstabLaplace_bounds t ht).1]
  rw [← log_buchstabLaplace_eq_exponentialIntegral t ht, Real.exp_log hp]
  ring

theorem tendsto_mul_buchstabLaplace_euler :
    Tendsto (fun t => t * buchstabLaplace t) (𝓝[>] 0)
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  have h := (Real.continuous_exp.tendsto _ |>.comp tendsto_exponentialIntegral_add_log).sub
    (show Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) from tendsto_id.mono_left inf_le_left)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  dsimp only [Function.comp_def]
  rw [Real.exp_add, Real.exp_log ht, buchstabLaplace_eq_exp_exponentialIntegral t ht]
  ring

end Chen.LinearSieve
