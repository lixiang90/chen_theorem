import ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryMonotonicity
import ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryError

open Filter Set

namespace Chen.LinearSieve

theorem inflatedAuxiliaryError_transport_of_antitone (d δ D s t B : ℝ)
    (H : ℝ → ℝ) (hD : 1 < D) (hs : 3 ≤ s) (hst : s ≤ t) (ht : t ≤ B)
    (hanti : AntitoneOn (fun u => shiftedAuxiliaryInflation d D 0 u * (u ^ 2 * H u)) (Icc 3 B)) :
    inflatedAuxiliaryError d δ D t H ≤ (s / t) * inflatedAuxiliaryError d δ D s H := by
  have h := hanti ⟨hs, hst.trans ht⟩ ⟨hs.trans hst, ht⟩ hst
  simp only [shiftedAuxiliaryInflation, add_zero] at h
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (Real.log_pos hD).le (-δ))
  have ht0 : 0 < t := by linarith
  apply (mul_le_mul_iff_left₀ ht0).mp
  unfold inflatedAuxiliaryError auxiliaryInflation auxiliaryErrorScale
  convert! hm using 1 <;> field_simp

/-- Moving towards the growing cutoff costs at most the ratio `s/t`.
This is the factor that cancels the sieve product ratio in the prefix. -/
theorem eventually_inflatedAuxiliaryError_transport (d δ : ℝ) (hd : 0 < d) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ s t : ℝ, 3 ≤ s → s ≤ t →
      t ≤ 2 * growingSieveParameter d (Real.log D) →
      (inflatedAuxiliaryError d δ D t upperAuxiliaryError ≤
        (s / t) * inflatedAuxiliaryError d δ D s upperAuxiliaryError) ∧
      (inflatedAuxiliaryError d δ D t lowerAuxiliaryError ≤
        (s / t) * inflatedAuxiliaryError d δ D s lowerAuxiliaryError) := by
  filter_upwards [eventually_inflatedAuxiliary_antitone d hd] with D hD
  refine ⟨hD.1, ?_⟩
  intro s t hs hst ht
  have hanti := hD.2 0 (by norm_num) (by norm_num)
  exact ⟨inflatedAuxiliaryError_transport_of_antitone d δ D s t _ _ hD.1 hs hst ht hanti.1,
    inflatedAuxiliaryError_transport_of_antitone d δ D s t _ _ hD.1 hs hst ht hanti.2⟩

end Chen.LinearSieve
