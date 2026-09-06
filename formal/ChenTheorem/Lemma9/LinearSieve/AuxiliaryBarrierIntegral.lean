import ChenTheorem.Lemma9.LinearSieve.AuxiliaryBarrierKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Set MeasureTheory

namespace Chen.LinearSieve

noncomputable def auxiliaryBarrierIntegral (a C s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, auxiliaryAdjoint (s + u) *
    Real.exp (auxiliaryBarrierPhase a C (s - 1) - auxiliaryBarrierPhase a C (s - 1 + u))

theorem continuousOn_auxiliaryBarrierKernel (a C s : ℝ) (hs : 4 ≤ s) :
    ContinuousOn (fun u => auxiliaryAdjoint (s + u) *
      Real.exp (auxiliaryBarrierPhase a C (s - 1) - auxiliaryBarrierPhase a C (s - 1 + u)))
        (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.mul (by unfold auxiliaryAdjoint; fun_prop)
  apply Real.continuous_exp.comp_continuousOn
  apply ContinuousOn.sub continuousOn_const
  exact (continuousOn_auxiliaryBarrierPhase a C).comp
    (continuousOn_const.add continuousOn_id)
    (by intro u hu; change 0 < s - 1 + u; linarith [hu.1])

theorem integral_exp_neg_mul_unit (v : ℝ) (hv : v ≠ 0) :
    (∫ u in (0 : ℝ)..1, Real.exp (-v * u)) = (1 - Real.exp (-v)) / v := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hv), integral_exp]
  simp only [mul_one, mul_zero, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

theorem auxiliaryBarrierIntegral_upper (a C s : ℝ)
    (ha : 0 ≤ a) (hs : 4 ≤ s)
    (hv : auxiliaryBarrierSlope a C s - (2 * a + 4) / s ≠ 0) :
    auxiliaryBarrierIntegral a C s ≤ auxiliaryAdjoint s *
      ((1 - Real.exp (-(auxiliaryBarrierSlope a C s - (2 * a + 4) / s))) /
        (auxiliaryBarrierSlope a C s - (2 * a + 4) / s)) := by
  have hc : Continuous (fun u : ℝ => auxiliaryAdjoint s *
      Real.exp (-(auxiliaryBarrierSlope a C s - (2 * a + 4) / s) * u)) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((continuousOn_auxiliaryBarrierKernel a C s hs).intervalIntegrable_of_Icc (by norm_num))
    (hc.intervalIntegrable _ _)
    (fun u hu => auxiliaryBarrier_kernel_upper a C s u ha hs hu.1 hu.2)
  rw [intervalIntegral.integral_const_mul, integral_exp_neg_mul_unit _ hv] at hi
  exact hi

theorem auxiliaryErrorSum_le_barrier_of_weight_le (a C u t : ℝ)
    (h : auxiliaryBarrierWeight a C t ≤ auxiliaryBarrierWeight a C u) :
    auxiliaryErrorSum t ≤ auxiliaryErrorSum u *
      Real.exp (auxiliaryBarrierPhase a C u - auxiliaryBarrierPhase a C t) := by
  rw [auxiliaryBarrierWeight, auxiliaryBarrierWeight,
    ← le_div_iff₀ (Real.exp_pos (auxiliaryBarrierPhase a C t))] at h
  simpa only [Real.exp_sub, mul_div_assoc] using h

/-- Monotonicity up to a candidate stationary point bounds the scalar
pairing by the explicit comparison kernel. -/
theorem auxiliaryBarrier_pairing_bound_of_antitone (a C s : ℝ) (hs : 4 ≤ s)
    (hanti : AntitoneOn (auxiliaryBarrierWeight a C) (Icc (s - 1) s)) :
    s * auxiliaryAdjoint s * auxiliaryErrorSum s ≤
      auxiliaryErrorSum (s - 1) * auxiliaryBarrierIntegral a C s := by
  have hQ := continuousOn_auxiliaryErrorSum.comp
    (continuousOn_const.add continuousOn_id)
    (show MapsTo (fun u => s - 1 + u) (Icc (0 : ℝ) 1) (Ioi 1) from by
      intro u hu; change 1 < s - 1 + u; linarith [hu.1])
  have hq : Continuous (fun u : ℝ => auxiliaryAdjoint (s + u)) := by
    unfold auxiliaryAdjoint
    fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((hq.continuousOn.mul hQ).intervalIntegrable_of_Icc (by norm_num))
    (((continuousOn_auxiliaryBarrierKernel a C s hs).const_mul
      (auxiliaryErrorSum (s - 1))).intervalIntegrable_of_Icc (by norm_num))
    (show ∀ u ∈ Icc (0 : ℝ) 1,
      auxiliaryAdjoint (s + u) * auxiliaryErrorSum (s - 1 + u) ≤
        auxiliaryErrorSum (s - 1) * (auxiliaryAdjoint (s + u) *
          Real.exp (auxiliaryBarrierPhase a C (s - 1) - auxiliaryBarrierPhase a C (s - 1 + u))) from by
      intro u hu
      have hw := hanti (show s - 1 ∈ Icc (s - 1) s by constructor <;> linarith)
        (show s - 1 + u ∈ Icc (s - 1) s by constructor <;> linarith [hu.1, hu.2])
        (by linarith [hu.1])
      have he := mul_le_mul_of_nonneg_left
        (auxiliaryErrorSum_le_barrier_of_weight_le a C (s - 1) (s - 1 + u) hw)
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

theorem auxiliaryBarrier_stationary_constraint (a C s : ℝ)
    (ha : 0 ≤ a) (hs : 4 ≤ s)
    (hv : auxiliaryBarrierSlope a C s - (2 * a + 4) / s ≠ 0)
    (hanti : AntitoneOn (auxiliaryBarrierWeight a C) (Icc (s - 1) s))
    (hstat : deriv (auxiliaryBarrierWeight a C) s = 0) :
    1 ≤ (auxiliaryBarrierSlope a C s - 2 / s) *
      ((1 - Real.exp (-(auxiliaryBarrierSlope a C s - (2 * a + 4) / s))) /
        (auxiliaryBarrierSlope a C s - (2 * a + 4) / s)) := by
  have h := auxiliaryBarrier_pairing_bound_of_antitone a C s hs hanti
  have hb := mul_le_mul_of_nonneg_left (auxiliaryBarrierIntegral_upper a C s ha hs hv)
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
