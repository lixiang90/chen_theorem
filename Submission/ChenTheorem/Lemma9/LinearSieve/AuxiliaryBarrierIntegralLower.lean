import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryBarrierKernelLower
import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryBarrierIntegral

set_option autoImplicit true
open Set MeasureTheory

namespace Chen.LinearSieve

theorem integral_exp_neg_mul_half (v : ℝ) (hv : v ≠ 0) :
    (∫ u in (0 : ℝ)..(1 / 2), Real.exp (-v * u)) = (1 - Real.exp (-v / 2)) / v := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hv), integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul, mul_one_div]
  field_simp
  ring

theorem auxiliaryBarrierIntegral_lower (a C s : ℝ)
    (ha : 0 ≤ a) (hs : 4 ≤ s)
    (hv : auxiliaryBarrierSlope a C s - (1 + a / 2) / s ≠ 0) :
    auxiliaryAdjoint s *
      ((1 - Real.exp (-(auxiliaryBarrierSlope a C s - (1 + a / 2) / s) / 2)) /
        (auxiliaryBarrierSlope a C s - (1 + a / 2) / s)) ≤
      auxiliaryBarrierIntegral a C s := by
  have hc := continuousOn_auxiliaryBarrierKernel a C s hs
  have hh := hc.mono (show Icc (0 : ℝ) (1 / 2) ⊆ Icc 0 1 from
    fun u hu => ⟨hu.1, by linarith [hu.2]⟩)
  have he : Continuous (fun u : ℝ => auxiliaryAdjoint s *
      Real.exp (-(auxiliaryBarrierSlope a C s - (1 + a / 2) / s) * u)) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (he.intervalIntegrable _ _) (hh.intervalIntegrable_of_Icc (by norm_num))
    (fun u hu => auxiliaryBarrier_kernel_lower a C s u ha hs hu.1 hu.2)
  rw [intervalIntegral.integral_const_mul, integral_exp_neg_mul_half _ hv] at hi
  apply hi.trans
  apply intervalIntegral.integral_mono_interval le_rfl (by norm_num) (by norm_num)
  · exact (ae_restrict_mem measurableSet_Ioc).mono fun u hu =>
      mul_nonneg (auxiliaryAdjoint_pos (s + u) (by linarith [hu.1])).le (Real.exp_pos _).le
  · exact hc.intervalIntegrable_of_Icc (by norm_num)

theorem barrier_le_auxiliaryErrorSum_of_weight_le (a C u t : ℝ)
    (h : auxiliaryBarrierWeight a C u ≤ auxiliaryBarrierWeight a C t) :
    auxiliaryErrorSum u * Real.exp (auxiliaryBarrierPhase a C u - auxiliaryBarrierPhase a C t) ≤
      auxiliaryErrorSum t := by
  rw [auxiliaryBarrierWeight, auxiliaryBarrierWeight,
    ← div_le_iff₀ (Real.exp_pos (auxiliaryBarrierPhase a C t))] at h
  simpa only [Real.exp_sub, mul_div_assoc] using h

theorem auxiliaryBarrier_pairing_bound_of_monotone (a C s : ℝ) (hs : 4 ≤ s)
    (hmono : MonotoneOn (auxiliaryBarrierWeight a C) (Icc (s - 1) s)) :
    auxiliaryErrorSum (s - 1) * auxiliaryBarrierIntegral a C s ≤
      s * auxiliaryAdjoint s * auxiliaryErrorSum s := by
  have hQ := continuousOn_auxiliaryErrorSum.comp
    (continuousOn_const.add continuousOn_id)
    (show MapsTo (fun u => s - 1 + u) (Icc (0 : ℝ) 1) (Ioi 1) from by
      intro u hu; change 1 < s - 1 + u; linarith [hu.1])
  have hq : Continuous (fun u : ℝ => auxiliaryAdjoint (s + u)) := by
    unfold auxiliaryAdjoint
    fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (((continuousOn_auxiliaryBarrierKernel a C s hs).const_mul
      (auxiliaryErrorSum (s - 1))).intervalIntegrable_of_Icc (by norm_num))
    ((hq.continuousOn.mul hQ).intervalIntegrable_of_Icc (by norm_num))
    (show ∀ u ∈ Icc (0 : ℝ) 1,
      auxiliaryErrorSum (s - 1) * (auxiliaryAdjoint (s + u) *
          Real.exp (auxiliaryBarrierPhase a C (s - 1) - auxiliaryBarrierPhase a C (s - 1 + u))) ≤
        auxiliaryAdjoint (s + u) * auxiliaryErrorSum (s - 1 + u) from by
      intro u hu
      have hw := hmono (show s - 1 ∈ Icc (s - 1) s by constructor <;> linarith)
        (show s - 1 + u ∈ Icc (s - 1) s by constructor <;> linarith [hu.1, hu.2])
        (by linarith [hu.1])
      have he := mul_le_mul_of_nonneg_left
        (barrier_le_auxiliaryErrorSum_of_weight_le a C (s - 1) (s - 1 + u) hw)
        (auxiliaryAdjoint_pos (s + u) (by linarith [hu.1])).le
      convert! he using 1
      ring)
  simp only [Pi.mul_apply, Function.comp_def, Pi.add_apply, id_eq] at hi
  rw [intervalIntegral.integral_const_mul] at hi
  have ht := intervalIntegral.integral_comp_add_left
    (fun t => auxiliaryAdjoint (t + 1) * auxiliaryErrorSum t)
    (a := 0) (b := 1) (s - 1)
  simp only [add_zero, sub_add_cancel] at ht
  have he : (fun u => auxiliaryAdjoint (s - 1 + u + 1) * auxiliaryErrorSum (s - 1 + u)) =
      (fun u => auxiliaryAdjoint (s + u) * auxiliaryErrorSum (s - 1 + u)) := by
    funext u
    congr 2
    ring
  rw [he, ← auxiliaryErrorSum_pairing_zero s (by linarith)] at ht
  rw [ht] at hi
  exact hi

theorem auxiliaryBarrier_stationary_upper_constraint (a C s : ℝ)
    (ha : 0 ≤ a) (hs : 4 ≤ s)
    (hv : auxiliaryBarrierSlope a C s - (1 + a / 2) / s ≠ 0)
    (hmono : MonotoneOn (auxiliaryBarrierWeight a C) (Icc (s - 1) s))
    (hstat : deriv (auxiliaryBarrierWeight a C) s = 0) :
    (auxiliaryBarrierSlope a C s - 2 / s) *
      ((1 - Real.exp (-(auxiliaryBarrierSlope a C s - (1 + a / 2) / s) / 2)) /
        (auxiliaryBarrierSlope a C s - (1 + a / 2) / s)) ≤ 1 := by
  have h := auxiliaryBarrier_pairing_bound_of_monotone a C s hs hmono
  have hb := mul_le_mul_of_nonneg_left (auxiliaryBarrierIntegral_lower a C s ha hs hv)
    (auxiliaryErrorSum_pos (s - 1) (by linarith)).le
  have hr := (auxiliaryBarrierWeight_stationary_iff a C s (by linarith)).mp hstat
  have he : auxiliaryErrorSum (s - 1) =
      (auxiliaryBarrierSlope a C s - 2 / s) * (s * auxiliaryErrorSum s) := by
    exact (div_eq_iff (mul_pos (show 0 < s by linarith)
      (auxiliaryErrorSum_pos s (by linarith))).ne').mp hr
  have hp := mul_pos (mul_pos (show 0 < s by linarith)
    (auxiliaryAdjoint_pos s (by linarith))) (auxiliaryErrorSum_pos s (by linarith))
  rw [he] at h hb
  nlinarith

end Chen.LinearSieve
