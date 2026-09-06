import ChenTheorem.Lemma9.LinearSieve.AbelRight
import ChenTheorem.Lemma9.LinearSieve.BuchstabError

open Finset MeasureTheory Set

namespace Chen.LinearSieve

/-- Integration by parts for continuous weights with integrable right
derivatives. In particular, the weight may have a corner at a sieve cutoff. -/
theorem buchstabTailMajorant_integral_eq_of_hasDeriv_right
    (K w z : ℝ) (hw : 2 ≤ w) (hwz : w ≤ z) (f g : ℝ → ℝ)
    (hfc : ContinuousOn f (Icc w z))
    (hfd : ∀ t ∈ Ioo w z, HasDerivWithinAt f (g t) (Ioi t) t)
    (hgi : IntegrableOn g (Icc w z)) :
    f w * buchstabTailMajorant K z w +
      (∫ t in Ioc w z, g t * buchstabTailMajorant K z t) =
        K * f z / Real.log z +
          ∫ t in Ioc w z, f t * buchstabDensityMajorant K z t := by
  have hMc := continuousOn_buchstabTailMajorant K w z hw
  have hDc := continuousOn_buchstabDensityMajorant K w z hw
  have hleft := hgi.mul_continuousOn hMc isCompact_Icc
  have hright : IntegrableOn (fun t => f t * buchstabDensityMajorant K z t) (Icc w z) :=
    (hfc.mul hDc).integrableOn_Icc
  have hparts := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hwz
    (hfc.mul hMc)
    (fun t ht => (hfd t ht).mul
      (hasDerivAt_buchstabTailMajorant K z t (by linarith [ht.1])).hasDerivWithinAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hwz).mpr
      (hleft.add (hfc.mul hDc.neg).integrableOn_Icc))
  have heq : (fun t => g t * buchstabTailMajorant K z t +
      f t * -buchstabDensityMajorant K z t) =
      (fun t => g t * buchstabTailMajorant K z t - f t * buchstabDensityMajorant K z t) := by
    funext t
    ring
  rw [heq, intervalIntegral.integral_of_le hwz,
    integral_sub (hleft.mono_set Ioc_subset_Icc_self)
      (hright.mono_set Ioc_subset_Icc_self)] at hparts
  have hlz : Real.log z ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hterminal : f z * buchstabTailMajorant K z z = K * f z / Real.log z := by
    simp only [buchstabTailMajorant, div_self hlz, mul_one, add_sub_cancel_left]
    ring
  dsimp only [Pi.mul_apply] at hparts
  rw [hterminal] at hparts
  linarith

/-- The same dimension-one estimate as the smooth version, now admitting
continuous piecewise smooth weights with an integrable right derivative. -/
theorem weighted_buchstab_partial_summation_of_hasDeriv_right :
    ∃ K : ℝ, 0 < K ∧ ∀ w : ℝ, ∀ z : ℕ, 2 ≤ w → w ≤ z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ f g : ℝ → ℝ, ContinuousOn f (Icc w (z : ℝ)) →
        (∀ t ∈ Ioo w (z : ℝ), HasDerivWithinAt f (g t) (Ioi t) t) →
        IntegrableOn g (Icc w (z : ℝ)) →
        (∀ t ∈ Icc w (z : ℝ), 0 ≤ f t) →
        (∀ t ∈ Icc w (z : ℝ), 0 ≤ g t) →
        (∀ t ∈ Icc w (z : ℝ), f t * Real.log z ≤ f z * Real.log t) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z, f p * buchstabCoefficient P z p) ≤
          Real.log z * (∫ t in Ioc w (z : ℝ), f t * logSieveKernel t) +
            2 * K * f z / Real.log w := by
  obtain ⟨K, hK, hbound⟩ := primeDensity_sieveProduct_real_dimension_one
  refine ⟨K, hK, ?_⟩
  intro w z hw hwz P hP hodd f g hfc hfd hgi hf hg hscale
  have htail : ∀ t ∈ Icc w (z : ℝ),
      coefficientTail (buchstabCoefficient P z) z t ≤ buchstabTailMajorant K z t := by
    intro t ht
    rw [coefficientTail_buchstab P hP hodd]
    have hb := hbound t z (hw.trans ht.1) ht.2 P hP hodd
    simpa only [Nat.floor_natCast, buchstabTailMajorant] using sub_le_sub_right hb 1
  have hMi := hgi.mul_continuousOn (continuousOn_buchstabTailMajorant K w z hw) isCompact_Icc
  have hb := sum_mul_le_coefficientTail_majorant_of_hasDeriv_right
    (buchstabCoefficient P z) w z (by linarith) hwz f g (buchstabTailMajorant K z)
      hfc hfd hgi (hf w ⟨le_rfl, hwz⟩) hg htail hMi
  rw [buchstabTailMajorant_integral_eq_of_hasDeriv_right K w z hw hwz f g hfc hfd hgi] at hb
  simp only [Nat.floor_natCast] at hb
  exact hb.trans (buchstab_density_error_le K w z hK.le hw hwz f hfc
    (hf z ⟨hwz, le_rfl⟩) hscale)

end Chen.LinearSieve
