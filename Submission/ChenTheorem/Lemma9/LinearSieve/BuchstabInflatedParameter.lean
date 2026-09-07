import Submission.ChenTheorem.Lemma9.LinearSieve.InflatedWeightRegularity
import Submission.ChenTheorem.Lemma9.LinearSieve.BuchstabMonotoneRight
import Submission.ChenTheorem.Lemma9.LinearSieve.InflatedPrimeWeight

set_option autoImplicit true
open Set MeasureTheory

namespace Chen.LinearSieve

/-- The inflated child majorant satisfies the parameter-form Buchstab bound.
The one-sided derivative accommodates the auxiliary junctions. -/
theorem weighted_buchstab_inflated_parameter_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ d δ a : ℝ, ∀ H S : ℝ → ℝ,
      0 ≤ a → ContinuousOn H (Ioi a) → (∀ s ∈ Ioi a, 0 ≤ H s) →
      (∀ s ∈ Ioi a, HasDerivWithinAt H (-(S s + 2 * H s) / s) (Iio s) s) →
      ∀ D w : ℝ, ∀ z : ℕ, 1 < D → 2 ≤ w → w ≤ z → a + 1 < sieveParameter D z →
      IntegrableOn (fun t => S (sieveParameter D t - 1)) (Icc w (z : ℝ)) →
      MonotoneOn (fun t => inflatedChildAuxiliaryWeight d δ D (sieveParameter D t) H) (Icc w (z : ℝ)) →
      (∀ t ∈ Icc w (z : ℝ),
        inflatedChildAuxiliaryWeight d δ D (sieveParameter D t) H * Real.log z ≤
          inflatedChildAuxiliaryWeight d δ D (sieveParameter D z) H * Real.log t) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z, inflatedChildAuxiliaryWeight d δ D (sieveParameter D p) H *
          buchstabCoefficient P z p) ≤
        (1 / sieveParameter D z) * (∫ s in Ioc (sieveParameter D z) (sieveParameter D w),
          inflatedChildAuxiliaryWeight d δ D s H) +
        2 * K * inflatedChildAuxiliaryWeight d δ D (sieveParameter D z) H / Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_partial_summation_monotone_right
  refine ⟨K, hK, ?_⟩
  intro d δ a H S ha hHc hHn hleft D w z hD hw hwz hs hSi hmono hscale P hP hodd
  have hpos : ∀ t ∈ Icc w (z : ℝ), a + 1 < sieveParameter D t :=
    fun t ht => hs.trans_le (sieveParameter_mem_Icc hD hw ht).1
  have hqc := continuousOn_inflatedChildAuxiliaryWeight d δ D a
    (sieveParameter D z) (sieveParameter D w) H hD ha hs hHc
  have hfc := hqc.comp (continuousOn_sieveParameter D w z hw)
    (fun t ht => sieveParameter_mem_Icc hD hw ht)
  have h := hb w z hw hwz P hP hodd _ (inflatedAuxiliaryPrimeSlope d δ H S D) hfc
    (fun t ht => hasDerivWithinAt_inflatedAuxiliaryPrimeWeight_right d δ D t H S hD
      (by linarith [ht.1]) (by linarith [hpos t ⟨ht.1.le, ht.2.le⟩])
      (hleft _ (by change a < sieveParameter D t - 1; linarith [hpos t ⟨ht.1.le, ht.2.le⟩])))
    (integrableOn_inflatedAuxiliaryPrimeSlope d δ D w z a H S hD hw ha hs hHc hSi)
    (fun t ht => inflatedChildAuxiliaryWeight_nonneg d δ D _ H hD
      (by linarith [hpos t ht]) (hHn _ (by change a < sieveParameter D t - 1; linarith [hpos t ht])))
    hmono hscale
  dsimp only [Function.comp_def] at h
  rwa [integral_sieveParameter_substitution D w z hD hw hwz _ hqc] at h

end Chen.LinearSieve
