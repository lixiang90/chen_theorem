import ChenTheorem.Lemma9.LinearSieve.BuchstabFunction
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open Set Filter MeasureTheory
open scoped Topology

namespace Chen.LinearSieve

noncomputable def buchstabLaplace (t : ℝ) : ℝ :=
  ∫ s in Ioi (1 : ℝ), buchstabFunction s * Real.exp (-t * s)

theorem integrableOn_mul_exp_neg (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun s : ℝ => s * Real.exp (-t * s)) (Ioi 1) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := 1) (p := 1) (by norm_num) le_rfl ht
  simp only [Real.rpow_one] at h
  exact h.mono_set (Ioi_subset_Ioi (by norm_num))

theorem integrableOn_buchstabLaplace (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun s => buchstabFunction s * Real.exp (-t * s)) (Ioi 1) := by
  apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos ht) 1).const_mul 2).mono'
  · exact ((continuousOn_buchstabFunction.mono Ioi_subset_Ici_self).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hb := buchstabFunction_bounds s hs.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right hb.2 (Real.exp_pos _).le

theorem integrableOn_buchstabLaplace_moment (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun s => s * buchstabFunction s * Real.exp (-t * s)) (Ioi 1) := by
  apply ((integrableOn_mul_exp_neg t ht).const_mul 2).mono'
  · exact ((continuousOn_id.mul (continuousOn_buchstabFunction.mono Ioi_subset_Ici_self)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hb := buchstabFunction_bounds s hs.le
    have hs0 : 0 ≤ s := by linarith [show 1 < s from hs]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hs0 hb.1) (Real.exp_pos _).le)]
    nlinarith [mul_le_mul_of_nonneg_left hb.2 (mul_nonneg hs0 (Real.exp_pos (-t * s)).le)]

theorem hasDerivAt_buchstabLaplace (t : ℝ) (ht : 0 < t) :
    HasDerivAt buchstabLaplace
      (-(∫ s in Ioi (1 : ℝ), s * buchstabFunction s * Real.exp (-t * s))) t := by
  let F : ℝ → ℝ → ℝ := fun x s => buchstabFunction s * Real.exp (-x * s)
  let F' : ℝ → ℝ → ℝ := fun x s => -(s * buchstabFunction s * Real.exp (-x * s))
  have hmeas (x : ℝ) : AEStronglyMeasurable (F x) (volume.restrict (Ioi 1)) :=
    ((continuousOn_buchstabFunction.mono Ioi_subset_Ici_self).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).aestronglyMeasurable measurableSet_Ioi
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun s => 2 * (s * Real.exp (-(t / 2) * s)))
    (Ioi_mem_nhds (show t / 2 < t by linarith))
    (Eventually.of_forall hmeas) (integrableOn_buchstabLaplace t ht)
    (integrableOn_buchstabLaplace_moment t ht).neg.aestronglyMeasurable
    ?_ ((integrableOn_mul_exp_neg (t / 2) (by positivity)).const_mul 2) ?_
  · unfold buchstabLaplace
    simpa only [F, F', integral_neg] using h.2
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    intro x hx
    have hb := buchstabFunction_bounds s hs.le
    have hs0 : 0 ≤ s := by linarith [show 1 < s from hs]
    have he : Real.exp (-x * s) ≤ Real.exp (-(t / 2) * s) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (by linarith [show t / 2 < x from hx]) hs0
    dsimp [F']
    rw [abs_neg, abs_of_nonneg (mul_nonneg (mul_nonneg hs0 hb.1) (Real.exp_pos _).le)]
    calc
      s * buchstabFunction s * Real.exp (-x * s)
          ≤ s * 2 * Real.exp (-(t / 2) * s) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hb.2 hs0) he (Real.exp_pos _).le (by positivity)
      _ = 2 * (s * Real.exp (-(t / 2) * s)) := by ring
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    intro x hx
    convert! (((hasDerivAt_id x).neg.mul_const s).exp.const_mul (buchstabFunction s)) using 1
    dsimp [F, F']
    ring

theorem buchstabLaplace_bounds (t : ℝ) (ht : 0 < t) :
    0 ≤ buchstabLaplace t ∧ buchstabLaplace t ≤ 2 * Real.exp (-t) / t := by
  constructor
  · apply setIntegral_nonneg measurableSet_Ioi
    intro s hs
    exact mul_nonneg (buchstabFunction_bounds s hs.le).1 (Real.exp_pos _).le
  · have hi := integral_mono_ae (integrableOn_buchstabLaplace t ht)
      ((integrableOn_exp_mul_Ioi (neg_neg_of_pos ht) 1).const_mul 2)
      (show ∀ᵐ s ∂volume.restrict (Ioi (1 : ℝ)),
        buchstabFunction s * Real.exp (-t * s) ≤ 2 * Real.exp (-t * s) from by
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
          exact mul_le_mul_of_nonneg_right (buchstabFunction_bounds s hs.le).2 (Real.exp_pos _).le)
    rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ht)] at hi
    unfold buchstabLaplace
    simpa only [mul_one, neg_div_neg_eq, mul_div_assoc] using hi

end Chen.LinearSieve
