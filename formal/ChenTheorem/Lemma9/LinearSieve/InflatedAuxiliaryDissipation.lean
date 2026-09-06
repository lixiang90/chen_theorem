import ChenTheorem.Lemma9.LinearSieve.InflationSlopeGap

open Filter

namespace Chen.LinearSieve

/-- Negative derivative of the inflated weighted parent, when its delay
equation holds. -/
noncomputable def inflatedAuxiliaryDissipation (d D t : ℝ) (H J : ℝ → ℝ) : ℝ :=
  auxiliaryInflation d D t * t *
    (J (t - 1) - auxiliaryInflationSlope d D 0 t * t * H t)

theorem inflatedChildWeight_le_dissipation (d δ D t B k : ℝ) (H J : ℝ → ℝ)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hD : 1 < D) (ht : 2 ≤ t) (htB : t ≤ B)
    (hH : 0 ≤ H t) (hJ : 0 ≤ J (t - 1))
    (hshift : k * t * Real.log t * H t ≤ J (t - 1))
    (hsl : auxiliaryInflationSlope d D 0 t ≤ k * Real.log t *
      inflationContractionGap (1 - δ) (t ^ d / Real.log D) t / 2) :
    inflatedChildAuxiliaryWeight d δ D t J ≤
      (1 - (1 - δ) / (4 * B)) * inflatedAuxiliaryDissipation d D t H J := by
  let x := t ^ d / Real.log D
  let g := inflationContractionGap (1 - δ) x t
  have ht0 : 0 < t := by linarith
  have hx : 0 ≤ x := div_nonneg (Real.rpow_nonneg ht0.le d) (Real.log_pos hD).le
  have hden : 0 < 1 + x := by linarith
  have hg := inflationContractionGap_bounds (1 - δ) x t (by linarith) (by linarith) hx (by linarith)
  have hc := inflationContractionGap_contraction (1 - δ) x t B (by linarith) (by linarith) hx ht htB
  have hI := (auxiliaryInflation_pos d D t hD ht0.le).le
  have hA : 0 ≤ auxiliaryInflation d D t * t * J (t - 1) := by positivity
  have h1 := mul_le_mul_of_nonneg_right hsl (mul_nonneg ht0.le hH)
  have h2 := mul_le_mul_of_nonneg_left hshift (div_nonneg hg.1 (by norm_num : (0 : ℝ) ≤ 2))
  have hder : auxiliaryInflationSlope d D 0 t * t * H t ≤ g * J (t - 1) / 2 := by
    dsimp [g, x] at h2 ⊢
    nlinarith
  have hw := childAuxiliaryWeight_linear_loss δ t hδ hδ1 (by linarith)
  have hq : inflatedChildAuxiliaryWeight d δ D t J ≤
      (auxiliaryInflation d D t * t * J (t - 1)) * (1 - g) := by
    rw [inflatedChildAuxiliaryWeight, auxiliaryChildInflation_eq_div d D t hD ht0.le]
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw (div_nonneg hI hden.le)) hJ
    change auxiliaryInflation d D t / (1 + x) * childAuxiliaryWeight δ t * J (t - 1) ≤ _
    calc
      _ ≤ auxiliaryInflation d D t / (1 + x) * (t - (1 - δ)) * J (t - 1) := hm
      _ = _ := by
        dsimp [g, inflationContractionGap]
        field_simp
        ring
  have hdiss : (auxiliaryInflation d D t * t * J (t - 1)) * (1 - g / 2) ≤
      inflatedAuxiliaryDissipation d D t H J := by
    have hm := mul_le_mul_of_nonneg_left hder (mul_nonneg hI ht0.le)
    dsimp [inflatedAuxiliaryDissipation]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hc.2 hA
  have hh := mul_le_mul_of_nonneg_left hdiss hc.1
  dsimp only [g] at hq hdiss hh
  nlinarith

theorem eventually_inflatedChildLower_dissipation (d δ : ℝ) (hd : 0 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ t B : ℝ, 3 ≤ t → t ≤ B →
      t ≤ 2 * growingSieveParameter d (Real.log D) →
      inflatedChildAuxiliaryWeight d δ D t lowerAuxiliaryError ≤
        (1 - (1 - δ) / (4 * B)) * inflatedAuxiliaryDissipation d D t upperAuxiliaryError lowerAuxiliaryError := by
  obtain ⟨k, K, hk, _, hshift⟩ := auxiliaryCrossShift_uniform_log_bounds
  filter_upwards [eventually_auxiliaryInflationSlope_gap d (1 - δ) k hd (by linarith) (by linarith) hk] with D hD
  refine ⟨hD.1, ?_⟩
  intro t B ht htB hcut
  exact inflatedChildWeight_le_dissipation d δ D t B k upperAuxiliaryError lowerAuxiliaryError hδ hδ1.le hD.1
    (by linarith) htB (upperAuxiliaryError_nonneg _ (by linarith)) (lowerAuxiliaryError_nonneg _ (by linarith))
    (hshift t ht).1.1 (hD.2 t (by linarith) hcut)

theorem eventually_inflatedChildUpper_dissipation (d δ : ℝ) (hd : 0 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ t B : ℝ, 2 < t → t ≤ B →
      t ≤ 2 * growingSieveParameter d (Real.log D) →
      inflatedChildAuxiliaryWeight d δ D t upperAuxiliaryError ≤
        (1 - (1 - δ) / (4 * B)) * inflatedAuxiliaryDissipation d D t lowerAuxiliaryError upperAuxiliaryError := by
  obtain ⟨k, K, hk, _, hshift⟩ := lowerAuxiliaryError_uniform_log_shift
  filter_upwards [eventually_auxiliaryInflationSlope_gap d (1 - δ) k hd (by linarith) (by linarith) hk] with D hD
  refine ⟨hD.1, ?_⟩
  intro t B ht htB hcut
  exact inflatedChildWeight_le_dissipation d δ D t B k lowerAuxiliaryError upperAuxiliaryError hδ hδ1.le hD.1
    ht.le htB (lowerAuxiliaryError_nonneg _ (by linarith)) (upperAuxiliaryError_nonneg _ (by linarith))
    (hshift t ht).1 (hD.2 t ht.le hcut)

end Chen.LinearSieve
