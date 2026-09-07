import Submission.ChenTheorem.Lemma9.LinearSieve.AuxiliaryInflation

set_option autoImplicit true
open Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The full auxiliary error scale, including the factor required when
the sieve parameter grows with the level. -/
noncomputable def inflatedAuxiliaryError (d δ D s : ℝ) (H : ℝ → ℝ) : ℝ :=
  auxiliaryInflation d D s * auxiliaryErrorScale δ D s H

theorem inflatedAuxiliaryError_nonneg (d δ D s : ℝ) (H : ℝ → ℝ)
    (hD : 1 < D) (hs : 0 ≤ s) (hH : 0 ≤ H s) :
    0 ≤ inflatedAuxiliaryError d δ D s H :=
  mul_nonneg (auxiliaryInflation_pos d D s hD hs).le
    (auxiliaryErrorScale_nonneg δ D s H hD hs hH)

theorem auxiliaryErrorScale_le_inflated (d δ D s : ℝ) (H : ℝ → ℝ)
    (hD : 1 < D) (hs : 0 ≤ s) (hH : 0 ≤ H s) :
    auxiliaryErrorScale δ D s H ≤ inflatedAuxiliaryError d δ D s H := by
  have h := mul_le_mul_of_nonneg_right (one_le_auxiliaryInflation d D s hD hs)
    (auxiliaryErrorScale_nonneg δ D s H hD hs hH)
  simpa only [one_mul, inflatedAuxiliaryError] using h

theorem inflatedAuxiliaryError_child_le (d δ D p : ℝ) (H : ℝ → ℝ)
    (hd : 1 ≤ d) (hD : 1 < D) (hp : 1 < p) (hs : 1 < sieveParameter D p)
    (hH : 0 ≤ H (sieveParameter D p - 1)) :
    inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) H ≤
      (Real.log D) ^ (-δ) * auxiliaryChildInflation d D (sieveParameter D p) *
        childAuxiliaryWeight δ (sieveParameter D p) * H (sieveParameter D p - 1) := by
  rw [inflatedAuxiliaryError, auxiliaryErrorScale_child δ D p H hD hp hs]
  have hn := mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (Real.log_pos hD).le (-δ))
      (childAuxiliaryWeight_nonneg δ _ hs)) hH
  have hm := mul_le_mul_of_nonneg_right (auxiliaryInflation_child_le d D p hd hD hp hs) hn
  calc
    _ ≤ auxiliaryChildInflation d D (sieveParameter D p) *
        ((Real.log D) ^ (-δ) * childAuxiliaryWeight δ (sieveParameter D p) *
          H (sieveParameter D p - 1)) := hm
    _ = _ := by ring

theorem tendsto_inflatedAuxiliaryError_zero (d δ s : ℝ) (H : ℝ → ℝ) (hδ : 0 < δ) :
    Tendsto (fun D => inflatedAuxiliaryError d δ D s H) atTop (𝓝 0) := by
  have h := (tendsto_auxiliaryInflation_one d s).mul (tendsto_auxiliaryErrorScale_zero δ s H hδ)
  simpa only [inflatedAuxiliaryError, mul_zero] using h

end Chen.LinearSieve
