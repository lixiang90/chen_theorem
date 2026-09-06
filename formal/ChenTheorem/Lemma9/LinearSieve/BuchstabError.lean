import ChenTheorem.Lemma9.LinearSieve.BuchstabIntegral

open Finset MeasureTheory

namespace Chen.LinearSieve

/-- The dimension-one logarithmic integration kernel. -/
noncomputable def logSieveKernel (t : ℝ) : ℝ := 1 / (t * Real.log t ^ 2)

theorem continuousOn_logSieveKernel (w z : ℝ) (hw : 2 ≤ w) :
    ContinuousOn logSieveKernel (Set.Icc w z) := by
  have ht0 : ∀ t ∈ Set.Icc w z, t ≠ 0 := fun t ht => ne_of_gt (by linarith [ht.1])
  have hlog := continuousOn_id.log ht0
  have hlog0 : ∀ t ∈ Set.Icc w z, Real.log t ≠ 0 :=
    fun t ht => (Real.log_pos (by linarith [ht.1])).ne'
  exact continuousOn_const.div (continuousOn_id.mul (hlog.pow 2))
    (fun t ht => mul_ne_zero (ht0 t ht) (pow_ne_zero _ (hlog0 t ht)))

theorem integral_logSieveKernel (w z : ℝ) (hw : 2 ≤ w) (hwz : w ≤ z) :
    (∫ t in Set.Ioc w z, logSieveKernel t) = 1 / Real.log w - 1 / Real.log z := by
  have hderiv : ∀ t ∈ Set.uIcc w z,
      HasDerivAt (fun t => -(1 / Real.log t)) (logSieveKernel t) t := by
    intro t ht
    rw [Set.uIcc_of_le hwz] at ht
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hlog0 : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    convert! ((hasDerivAt_const t (1 : ℝ)).fun_div (Real.hasDerivAt_log ht0) hlog0).neg using 1
    dsimp [logSieveKernel]
    field_simp
    ring
  have hi : IntegrableOn logSieveKernel (Set.Icc w z) :=
    (continuousOn_logSieveKernel w z hw).integrableOn_Icc
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hwz).mpr hi)
  rw [intervalIntegral.integral_of_le hwz] at h
  linarith

/-- Absorb the differentiated density correction using the logarithmic
growth bound on the weight. This retains an explicit `2 K f(z)/log w`. -/
theorem buchstab_density_error_le (K w z : ℝ) (hK : 0 ≤ K)
    (hw : 2 ≤ w) (hwz : w ≤ z) (f : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Icc w z)) (hfz : 0 ≤ f z)
    (hscale : ∀ t ∈ Set.Icc w z, f t * Real.log z ≤ f z * Real.log t) :
    K * f z / Real.log z + (∫ t in Set.Ioc w z, f t * buchstabDensityMajorant K z t) ≤
      Real.log z * (∫ t in Set.Ioc w z, f t * logSieveKernel t) + 2 * K * f z / Real.log w := by
  have hkc := continuousOn_logSieveKernel w z hw
  have hdc := continuousOn_buchstabDensityMajorant K w z hw
  have hfi : IntegrableOn (fun t => f t * buchstabDensityMajorant K z t) (Set.Icc w z) :=
    (hfc.mul hdc).integrableOn_Icc
  have hmi : IntegrableOn (fun t => Real.log z * (f t * logSieveKernel t) +
      (2 * K * f z) * logSieveKernel t) (Set.Icc w z) :=
    ((continuousOn_const.mul (hfc.mul hkc)).add (continuousOn_const.mul hkc)).integrableOn_Icc
  have hpoint : ∀ t ∈ Set.Ioc w z, f t * buchstabDensityMajorant K z t ≤
      Real.log z * (f t * logSieveKernel t) + (2 * K * f z) * logSieveKernel t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlog : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hs := mul_le_mul_of_nonneg_right (hscale t ⟨ht.1.le, ht.2⟩)
      (show 0 ≤ 2 * K / (t * Real.log t ^ 3) by positivity)
    have halgebra : f t * buchstabDensityMajorant K z t =
        Real.log z * (f t * logSieveKernel t) +
          (f t * Real.log z) * (2 * K / (t * Real.log t ^ 3)) := by
      dsimp [buchstabDensityMajorant, logSieveKernel]
      field_simp
    have halgebra' : (f z * Real.log t) * (2 * K / (t * Real.log t ^ 3)) =
        (2 * K * f z) * logSieveKernel t := by
      dsimp [logSieveKernel]
      field_simp
    rw [halgebra'] at hs
    rw [halgebra]
    exact _root_.add_le_add le_rfl hs
  have hint := setIntegral_mono_on (hfi.mono_set Set.Ioc_subset_Icc_self)
    (hmi.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc hpoint
  have hi1 : IntegrableOn (fun t => Real.log z * (f t * logSieveKernel t)) (Set.Icc w z) :=
    (continuousOn_const.mul (hfc.mul hkc)).integrableOn_Icc
  have hi2 : IntegrableOn (fun t => (2 * K * f z) * logSieveKernel t) (Set.Icc w z) :=
    (continuousOn_const.mul hkc).integrableOn_Icc
  rw [integral_add (hi1.mono_set Set.Ioc_subset_Icc_self)
    (hi2.mono_set Set.Ioc_subset_Icc_self), integral_const_mul, integral_const_mul,
    integral_logSieveKernel w z hw hwz] at hint
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hterm : 0 ≤ K * f z / Real.log z := by positivity
  have he : 2 * K * f z * (1 / Real.log w - 1 / Real.log z) =
      2 * K * f z / Real.log w - 2 * (K * f z / Real.log z) := by ring
  rw [he] at hint
  linarith

/-- Dimension-one partial summation for a differentiable nonnegative
increasing weight with `f(t)/log t ≤ f(z)/log z`. -/
theorem weighted_buchstab_partial_summation :
    ∃ K : ℝ, 0 < K ∧ ∀ w : ℝ, ∀ z : ℕ, 2 ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ f : ℝ → ℝ,
        (∀ t ∈ Set.Icc w (z : ℝ), DifferentiableAt ℝ f t) →
        IntegrableOn (deriv f) (Set.Icc w (z : ℝ)) →
        (∀ t ∈ Set.Icc w (z : ℝ), 0 ≤ f t) →
        (∀ t ∈ Set.Icc w (z : ℝ), 0 ≤ deriv f t) →
        (∀ t ∈ Set.Icc w (z : ℝ), f t * Real.log z ≤ f z * Real.log t) →
        (∑ p ∈ Ioc ⌊w⌋₊ z, f p * buchstabCoefficient P z p) ≤
          Real.log z * (∫ t in Set.Ioc w (z : ℝ), f t * logSieveKernel t) +
            2 * K * f z / Real.log w := by
  obtain ⟨K, hK, hbound⟩ := weighted_buchstab_density_bound
  refine ⟨K, hK, ?_⟩
  intro w z hw hwz P hP hodd f hfd hfi hf hfderiv hscale
  apply (hbound w z hw hwz P hP hodd f hfd hfi (hf w ⟨le_rfl, hwz⟩) hfderiv).trans
  exact buchstab_density_error_le K w z hK.le hw hwz f
    (fun t ht => (hfd t ht).continuousAt.continuousWithinAt) (hf z ⟨hwz, le_rfl⟩) hscale

end Chen.LinearSieve
