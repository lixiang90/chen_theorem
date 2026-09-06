import ChenTheorem.Lemma9.LinearSieve.EulerGammaIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Set Filter MeasureTheory
open scoped Topology

namespace Chen.LinearSieve

noncomputable def exponentialIntegral (t : ℝ) : ℝ :=
  ∫ u in Ioi t, Real.exp (-u) / u

theorem integrableOn_exponentialIntegral (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun u => Real.exp (-u) / u) (Ioi t) := by
  apply ((integrableOn_exp_neg_Ioi t).div_const t).mono'
  · exact (Real.measurable_exp.comp measurable_neg |>.div measurable_id).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans ht hu
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) hu0)]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le ht hu.le

theorem exponentialIntegral_log_identity (t : ℝ) (ht : 0 < t) :
    exponentialIntegral t = -Real.exp (-t) * Real.log t +
      ∫ u in Ioi t, Real.log u * Real.exp (-u) := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) u := by
    simpa using (hasDerivAt_id u).neg.exp
  have hi : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi t) :=
    integrableOn_log_mul_exp_neg.mono_set (Ioi_subset_Ioi ht.le)
  have hzero : Tendsto (fun u : ℝ => Real.exp (-u) * Real.log u)
      (𝓝[>] t) (𝓝 (Real.exp (-t) * Real.log t)) :=
    ((Real.continuous_exp.comp continuous_neg).continuousAt.mul
      (Real.continuousAt_log ht.ne')).tendsto.mono_left inf_le_left
  have hinfty : Tendsto (fun u : ℝ => Real.exp (-u) * Real.log u) atTop (𝓝 0) := by
    have hlog : (fun u : ℝ => Real.log u) =O[atTop] (fun u => u) :=
      Real.isLittleO_log_id_atTop.isBigO
    have hexp : Tendsto (fun u : ℝ => u * Real.exp (-u)) atTop (𝓝 0) := by
      simpa only [Real.rpow_one, neg_one_mul] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) 1 (by norm_num)
    have ho := hlog.mul (Asymptotics.isBigO_refl (fun u : ℝ => Real.exp (-u)) atTop)
    simpa only [mul_comm] using ho.trans_tendsto hexp
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun u : ℝ => Real.exp (-u)) (u' := fun u => -Real.exp (-u))
    (v := Real.log) (v' := fun u => 1 / u)
    (fun u _ => hd u) (fun u hu => by simpa only [one_div] using Real.hasDerivAt_log (ne_of_gt (lt_trans ht hu)))
    (by simpa only [Pi.mul_def, mul_one_div] using integrableOn_exponentialIntegral t ht)
    (by simpa only [Pi.mul_def, Pi.neg_def, neg_mul, mul_comm] using hi.neg)
    hzero hinfty
  simp only [mul_one_div, neg_mul, integral_neg, zero_sub] at h
  unfold exponentialIntegral
  simpa only [sub_neg_eq_add, mul_comm, neg_mul] using h

theorem tendsto_one_sub_exp_neg_mul_log_zero :
    Tendsto (fun t : ℝ => (1 - Real.exp (-t)) * Real.log t) (𝓝[>] 0) (𝓝 0) := by
  have hlog : Tendsto (fun t : ℝ => -(Real.log t * t)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, neg_zero] using
      (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1)).neg
  apply squeeze_zero_norm' ?_ hlog
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht ht1
  have ht0 : 0 < t := ht
  have he : 0 ≤ 1 - Real.exp (-t) := by
    linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht0.le)]
  have he' : 1 - Real.exp (-t) ≤ t := by linarith [Real.add_one_le_exp (-t)]
  have hl : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1.le
  rw [Real.norm_eq_abs, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos he hl)]
  nlinarith [mul_le_mul_of_nonpos_right he' hl]

theorem tendsto_exponentialIntegral_add_log :
    Tendsto (fun t => exponentialIntegral t + Real.log t)
      (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant)) := by
  have htail := integrableOn_log_mul_exp_neg.continuousWithinAt_Ici_primitive_Ioi
  have ht : Tendsto (fun t : ℝ => ∫ u in Ioi t, Real.log u * Real.exp (-u))
      (𝓝[>] 0) (𝓝 (-Real.eulerMascheroniConstant)) := by
    rw [← integral_log_mul_exp_neg_eq_neg_eulerMascheroni]
    exact htail.mono Ioi_subset_Ici_self
  have h := tendsto_one_sub_exp_neg_mul_log_zero.add ht
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [exponentialIntegral_log_identity t ht]
  ring

end Chen.LinearSieve
