import ChenTheorem.Lemma9.LinearSieve.BuchstabLaplace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Set Filter MeasureTheory
open scoped Topology

namespace Chen.LinearSieve

theorem integrableOn_buchstabLaplace_shift (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun s => buchstabFunction (s - 1) * Real.exp (-t * s)) (Ioi 2) := by
  apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos ht) 2).const_mul 2).mono'
  · exact ((continuousOn_buchstabFunction.comp (continuousOn_id.sub continuousOn_const)
      (fun s hs => by change 1 ≤ s - 1; linarith [show 2 < s from hs])).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hb := buchstabFunction_bounds (s - 1) (by linarith [show 2 < s from hs])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right hb.2 (Real.exp_pos _).le

theorem integral_buchstabLaplace_shift (t : ℝ) (ht : 0 < t) :
    (∫ s in Ioi (2 : ℝ), buchstabFunction (s - 1) * Real.exp (-t * s)) =
      Real.exp (-t) * buchstabLaplace t := by
  have hleft := intervalIntegral_tendsto_integral_Ioi 2
    (integrableOn_buchstabLaplace_shift t ht) tendsto_id
  have hright := (intervalIntegral_tendsto_integral_Ioi 1
    (integrableOn_buchstabLaplace t ht)
      (show Tendsto (fun b : ℝ => b - 1) atTop atTop from tendsto_atTop_add_const_right atTop (-1) tendsto_id)).const_mul (Real.exp (-t))
  have heq (b : ℝ) : (∫ s in (2 : ℝ)..b, buchstabFunction (s - 1) * Real.exp (-t * s)) =
      Real.exp (-t) * ∫ s in (1 : ℝ)..(b - 1), buchstabFunction s * Real.exp (-t * s) := by
    have hf (s : ℝ) : buchstabFunction (s - 1) * Real.exp (-t * s) =
        Real.exp (-t) * (buchstabFunction (s - 1) * Real.exp (-t * (s - 1))) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    simp_rw [hf]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun s => buchstabFunction s * Real.exp (-t * s)) 1]
    norm_num
  exact tendsto_nhds_unique hleft (hright.congr (fun b => (heq b).symm))

theorem tendsto_weighted_buchstab_exp_zero (t : ℝ) (ht : 0 < t) :
    Tendsto (fun s => (s * buchstabFunction s) * Real.exp (-t * s)) atTop (𝓝 0) := by
  have hm : Tendsto (fun s : ℝ => s * Real.exp (-t * s)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 t ht
  have h := hm.mul tendsto_buchstabFunction
  simp only [zero_mul] at h
  convert! h using 1
  funext s
  ring

theorem buchstabLaplace_tail_moment (t : ℝ) (ht : 0 < t) :
    t * (∫ s in Ioi (2 : ℝ), s * buchstabFunction s * Real.exp (-t * s)) =
      Real.exp (-t * 2) + Real.exp (-t) * buchstabLaplace t := by
  have hmoment := (integrableOn_buchstabLaplace_moment t ht).mono_set
    (Ioi_subset_Ioi (by norm_num : (1 : ℝ) ≤ 2))
  have hzero : Tendsto (fun s => (s * buchstabFunction s) * Real.exp (-t * s))
      (𝓝[>] 2) (𝓝 (Real.exp (-t * 2))) := by
    have hb : ContinuousAt buchstabFunction 2 :=
      continuousOn_buchstabFunction.continuousAt (Ici_mem_nhds (by norm_num))
    have hc : ContinuousAt (fun s => (s * buchstabFunction s) * Real.exp (-t * s)) 2 :=
      (continuousAt_id.mul hb).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt
    simpa only [buchstabFunction_initial 2 le_rfl, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
      one_mul] using hc.tendsto.mono_left (show 𝓝[>] (2 : ℝ) ≤ 𝓝 2 from inf_le_left)
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun s => s * buchstabFunction s) (u' := fun s => buchstabFunction (s - 1))
    (v := fun s => Real.exp (-t * s)) (v' := fun s => -t * Real.exp (-t * s))
    (fun s hs => hasDerivAt_mul_buchstabFunction s hs)
    (fun s _ => by simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id s).const_mul (-t)).exp)
    (by
      change IntegrableOn (fun s => (s * buchstabFunction s) * (-t * Real.exp (-t * s))) (Ioi 2)
      exact (hmoment.const_mul (-t)).congr (Eventually.of_forall (fun s => by ring)))
    (integrableOn_buchstabLaplace_shift t ht) hzero (tendsto_weighted_buchstab_exp_zero t ht)
  have heq : (∫ s in Ioi (2 : ℝ), (s * buchstabFunction s) * (-t * Real.exp (-t * s))) =
      -t * (∫ s in Ioi (2 : ℝ), s * buchstabFunction s * Real.exp (-t * s)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => by ring)
  rw [heq, integral_buchstabLaplace_shift t ht] at h
  linarith

theorem buchstabLaplace_initial_moment (t : ℝ) (ht : 0 < t) :
    t * (∫ s in (1 : ℝ)..2, s * buchstabFunction s * Real.exp (-t * s)) =
      Real.exp (-t) - Real.exp (-t * 2) := by
  have heq : (∫ s in (1 : ℝ)..2, s * buchstabFunction s * Real.exp (-t * s)) =
      ∫ s in (1 : ℝ)..2, Real.exp (-t * s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hs
    dsimp only
    rw [buchstabFunction_initial s hs.2, mul_one_div_cancel (by linarith [hs.1] : s ≠ 0), one_mul]
  rw [heq]
  have hd (s : ℝ) : HasDerivAt (fun s => -Real.exp (-t * s) / t) (Real.exp (-t * s)) s := by
    convert! (((hasDerivAt_id s).const_mul (-t)).exp.neg.div_const t) using 1
    simp only [id_eq]
    field_simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable 1 2)
  rw [h]
  field_simp
  ring

theorem buchstabLaplace_moment_equation (t : ℝ) (ht : 0 < t) :
    t * (∫ s in Ioi (1 : ℝ), s * buchstabFunction s * Real.exp (-t * s)) =
      Real.exp (-t) * (1 + buchstabLaplace t) := by
  have hi := integrableOn_buchstabLaplace_moment t ht
  rw [← intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi (by norm_num : (1 : ℝ) ≤ 2))), mul_add,
    buchstabLaplace_initial_moment t ht, buchstabLaplace_tail_moment t ht]
  ring

theorem hasDerivAt_buchstabLaplace_equation (t : ℝ) (ht : 0 < t) :
    HasDerivAt buchstabLaplace (-Real.exp (-t) / t * (1 + buchstabLaplace t)) t := by
  apply (hasDerivAt_buchstabLaplace t ht).congr_deriv
  have h := buchstabLaplace_moment_equation t ht
  have hJ : (∫ s in Ioi (1 : ℝ), s * buchstabFunction s * Real.exp (-t * s)) =
      Real.exp (-t) * (1 + buchstabLaplace t) / t :=
    (eq_div_iff ht.ne').mpr (by nlinarith [h])
  rw [hJ]
  ring

end Chen.LinearSieve
