import Submission.ChenTheorem.Lemma9.LinearSieve.BuchstabInflatedParameter

set_option autoImplicit true
open Set MeasureTheory Filter

namespace Chen.LinearSieve

/-- A uniform dimension-one constant for the actual lower-child majorant.
All regularity and shape hypotheses have been discharged. -/
theorem weighted_buchstab_inflated_lower :
    ∃ K : ℝ, 0 < K ∧ ∀ d δ : ℝ, 0 < d → -1 ≤ δ → ∀ᶠ D in atTop,
      ∀ w : ℝ, ∀ z : ℕ, 2 ≤ w → w ≤ z → 3 ≤ sieveParameter D z →
      sieveParameter D w ≤ 2 * growingSieveParameter d (Real.log D) + 1 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
        inflatedChildAuxiliaryWeight d δ D (sieveParameter D p) lowerAuxiliaryError * buchstabCoefficient P z p) ≤
      (1 / sieveParameter D z) * (∫ s in Ioc (sieveParameter D z) (sieveParameter D w),
        inflatedChildAuxiliaryWeight d δ D s lowerAuxiliaryError) +
      2 * K * inflatedChildAuxiliaryWeight d δ D (sieveParameter D z) lowerAuxiliaryError / Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_inflated_parameter_bound
  refine ⟨K, hK, ?_⟩
  intro d δ hd hδ
  filter_upwards [eventually_inflatedPrimeLowerWeight_shape d δ hd hδ] with D hshape
  intro w z hw hwz hs hcut P hP hodd
  have hu : ContinuousOn (fun t => sieveParameter D t - 1) (Icc w (z : ℝ)) :=
    (continuousOn_sieveParameter D w z hw).sub continuousOn_const
  have hum : Measurable (fun t => sieveParameter D t - 1) := by unfold sieveParameter; fun_prop
  have hSi := integrableOn_lowerAuxiliaryLeftSource_comp w z _ hu hum
  have h := hshape.2 w z hw hwz hs hcut
  exact hb d δ 0 lowerAuxiliaryError lowerAuxiliaryLeftSource le_rfl
    continuousOn_lowerAuxiliaryError (fun s hs => lowerAuxiliaryError_nonneg s hs)
    (fun s hs => hasDerivWithinAt_lowerAuxiliaryError_left s hs)
    D w z hshape.1 hw hwz (by linarith) hSi h.1 h.2 P hP hodd

/-- The upper-child version covers the entire lower-sieve domain `s>2`,
including the corner at child parameter three. -/
theorem weighted_buchstab_inflated_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ d δ : ℝ, 0 < d → -1 < δ → ∀ᶠ D in atTop,
      ∀ w : ℝ, ∀ z : ℕ, 2 ≤ w → w ≤ z → 2 < sieveParameter D z →
      sieveParameter D w ≤ 2 * growingSieveParameter d (Real.log D) + 1 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
        inflatedChildAuxiliaryWeight d δ D (sieveParameter D p) upperAuxiliaryError * buchstabCoefficient P z p) ≤
      (1 / sieveParameter D z) * (∫ s in Ioc (sieveParameter D z) (sieveParameter D w),
        inflatedChildAuxiliaryWeight d δ D s upperAuxiliaryError) +
      2 * K * inflatedChildAuxiliaryWeight d δ D (sieveParameter D z) upperAuxiliaryError / Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_inflated_parameter_bound
  refine ⟨K, hK, ?_⟩
  intro d δ hd hδ
  filter_upwards [eventually_inflatedPrimeUpperWeight_shape d δ hd hδ] with D hshape
  intro w z hw hwz hs hcut P hP hodd
  have hu : ContinuousOn (fun t => sieveParameter D t - 1) (Icc w (z : ℝ)) :=
    (continuousOn_sieveParameter D w z hw).sub continuousOn_const
  have hum : Measurable (fun t => sieveParameter D t - 1) := by unfold sieveParameter; fun_prop
  have hSi := integrableOn_upperAuxiliaryLeftSource_comp w z _ hu hum
  have h := hshape.2 w z hw hwz hs hcut
  exact hb d δ 1 upperAuxiliaryError upperAuxiliaryLeftSource (by norm_num)
    continuousOn_upperAuxiliaryError (fun s hs => upperAuxiliaryError_nonneg s hs)
    (fun s hs => hasDerivWithinAt_upperAuxiliaryError_left s hs)
    D w z hshape.1 hw hwz (by linarith) hSi h.1 h.2 P hP hodd

end Chen.LinearSieve
