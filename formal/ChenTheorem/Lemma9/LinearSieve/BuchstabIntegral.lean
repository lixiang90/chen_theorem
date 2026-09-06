import ChenTheorem.Lemma9.LinearSieve.WeightedBuchstab
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open Finset MeasureTheory

namespace Chen.LinearSieve

/-- The density obtained by differentiating the continuous tail bound. -/
noncomputable def buchstabDensityMajorant (K z t : ℝ) : ℝ :=
  Real.log z / (t * Real.log t ^ 2) * (1 + 2 * K / Real.log t)

theorem hasDerivAt_buchstabTailMajorant (K z t : ℝ) (ht : 1 < t) :
    HasDerivAt (buchstabTailMajorant K z) (-buchstabDensityMajorant K z t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog0 : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hlog := Real.hasDerivAt_log ht0
  have hK := (hasDerivAt_const t K).fun_div hlog hlog0
  have hz := (hasDerivAt_const t (Real.log z)).fun_div hlog hlog0
  convert! ((hK.const_add 1).mul hz).sub_const 1 using 1
  dsimp [buchstabDensityMajorant]
  field_simp
  ring

theorem continuousOn_buchstabDensityMajorant (K w z : ℝ) (hw : 2 ≤ w) :
    ContinuousOn (buchstabDensityMajorant K z) (Set.Icc w z) := by
  have ht0 : ∀ t ∈ Set.Icc w z, t ≠ 0 := fun t ht => ne_of_gt (by linarith [ht.1])
  have hlog := continuousOn_id.log ht0
  have hlog0 : ∀ t ∈ Set.Icc w z, Real.log t ≠ 0 :=
    fun t ht => (Real.log_pos (by linarith [ht.1])).ne'
  exact (continuousOn_const.div (continuousOn_id.mul (hlog.pow 2))
    (fun t ht => mul_ne_zero (ht0 t ht) (pow_ne_zero _ (hlog0 t ht)))).mul
      (continuousOn_const.add (continuousOn_const.div hlog hlog0))

/-- Integration by parts expresses the weighted tail bound using a
continuous density and its terminal boundary contribution. -/
theorem buchstabTailMajorant_integral_eq (K w z : ℝ) (hw : 2 ≤ w) (hwz : w ≤ z)
    (f : ℝ → ℝ) (hfd : ∀ t ∈ Set.Icc w z, DifferentiableAt ℝ f t)
    (hfi : IntegrableOn (deriv f) (Set.Icc w z)) :
    f w * buchstabTailMajorant K z w +
      (∫ t in Set.Ioc w z, deriv f t * buchstabTailMajorant K z t) =
        K * f z / Real.log z +
          ∫ t in Set.Ioc w z, f t * buchstabDensityMajorant K z t := by
  have hMc := continuousOn_buchstabDensityMajorant K w z hw
  have hMi : IntegrableOn (fun t => -buchstabDensityMajorant K z t) (Set.Icc w z) :=
    hMc.neg.integrableOn_Icc
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := buchstabTailMajorant K z) (u' := fun t => -buchstabDensityMajorant K z t)
    (v := f) (v' := deriv f)
    (fun t ht => hasDerivAt_buchstabTailMajorant K z t (by
      rw [Set.uIcc_of_le hwz] at ht
      linarith [ht.1]))
    (fun t ht => (hfd t (by simpa only [Set.uIcc_of_le hwz] using ht)).hasDerivAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hwz).mpr hMi)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hwz).mpr hfi)
  rw [intervalIntegral.integral_of_le hwz, intervalIntegral.integral_of_le hwz] at hparts
  have hleft : (∫ t in Set.Ioc w z, buchstabTailMajorant K z t * deriv f t) =
      ∫ t in Set.Ioc w z, deriv f t * buchstabTailMajorant K z t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    ring
  have hright : (∫ t in Set.Ioc w z, -buchstabDensityMajorant K z t * f t) =
      -(∫ t in Set.Ioc w z, f t * buchstabDensityMajorant K z t) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    ring
  have hlz : Real.log z ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hterminal : buchstabTailMajorant K z z * f z = K * f z / Real.log z := by
    simp only [buchstabTailMajorant, div_self hlz, mul_one, add_sub_cancel_left]
    ring
  rw [hleft, hright, hterminal] at hparts
  linarith

/-- Weighted comparison with a continuous main density and an explicit
`K/log` correction; no unproved linear-sieve functions enter the bound. -/
theorem weighted_buchstab_density_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ w : ℝ, ∀ z : ℕ, 2 ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ f : ℝ → ℝ,
        (∀ t ∈ Set.Icc w (z : ℝ), DifferentiableAt ℝ f t) →
        IntegrableOn (deriv f) (Set.Icc w (z : ℝ)) → 0 ≤ f w →
        (∀ t ∈ Set.Icc w (z : ℝ), 0 ≤ deriv f t) →
        (∑ p ∈ Ioc ⌊w⌋₊ z, f p * buchstabCoefficient P z p) ≤
          K * f z / Real.log z +
            ∫ t in Set.Ioc w (z : ℝ), f t * buchstabDensityMajorant K z t := by
  obtain ⟨K, hK, hbound⟩ := weighted_buchstab_dimension_one
  refine ⟨K, hK, ?_⟩
  intro w z hw hwz P hP hodd f hfd hfi hfw hfderiv
  have hb := hbound w z hw hwz P hP hodd f hfd hfi hfw hfderiv
  rwa [buchstabTailMajorant_integral_eq K w z hw hwz f hfd hfi] at hb

end Chen.LinearSieve
