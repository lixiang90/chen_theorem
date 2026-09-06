import ChenTheorem.Lemma9.LinearSieve.GrowingPrefixCutoff
import ChenTheorem.Lemma9.LinearSieve.GrowingPrefixRatio
import ChenTheorem.Lemma9.LinearSieve.RosserPrefixNormalization

open Filter

namespace Chen.LinearSieve

/-- The actual recursive prefix is bounded at its rounded cutoff by
the full auxiliary error, with an exponentially small factor. The
product ratio is retained explicitly for subsequent normalization. -/
theorem rosserPartialPrefix_growing_bound (d δ : ℝ) (hd : 2 < d) :
    ∀ᶠ D in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ N z : ℕ, ∀ upper : Bool,
      rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        (sieveProduct P primeDensity (growingPrefixIndex d D + 1) / sieveProduct P primeDensity (z + 1)) *
          Real.exp (-growingSieveParameter d (Real.log D)) * inflatedAuxiliaryError d δ D
            (sieveParameter D (growingPrefixIndex d D + 1)) upperAuxiliaryError ∧
      rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        (sieveProduct P primeDensity (growingPrefixIndex d D + 1) / sieveProduct P primeDensity (z + 1)) *
          Real.exp (-growingSieveParameter d (Real.log D)) * inflatedAuxiliaryError d δ D
            (sieveParameter D (growingPrefixIndex d D + 1)) lowerAuxiliaryError := by
  have hg := (tendsto_growingSieveParameter_atTop d (by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [eventually_growingPrefixCutoff_properties d (by linarith),
    rosserRelativeDefect_growing_parameter d δ hd, hg.eventually_ge_atTop 6] with D hc hb hσ
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  dsimp only [Function.comp_def] at hσ
  intro P hP hodd N z upper
  have hs : 6 ≤ sieveParameter D (growingPrefixIndex d D + 1) := hσ.trans hlo
  have hactive : ¬(upper = false ∧ D ≤ (((growingPrefixIndex d D + 1 : ℕ) : ℝ)) ^ 2) := by
    rintro ⟨_, h⟩
    exact (not_le.mpr hlevel) h
  have hprefix := rosserPartialPrefix_le_product_ratio_defect P hP hodd N z
    (growingPrefixIndex d D) upper D hactive
  have hsmall := hb (growingPrefixIndex d D) hm hlo P hP hodd upper
  have hratio : 0 ≤ sieveProduct P primeDensity (growingPrefixIndex d D + 1) /
      sieveProduct P primeDensity (z + 1) :=
    div_nonneg (primeDensity_sieveProduct_pos P hP hodd _).le
      (primeDensity_sieveProduct_pos P hP hodd _).le
  have he := Real.exp_le_exp.mpr (neg_le_neg hlo)
  have hstep : ∀ H : ℝ → ℝ,
      rosserRelativeDefect P (growingPrefixIndex d D + 1) upper D ≤
        Real.exp (-sieveParameter D (growingPrefixIndex d D + 1)) *
          inflatedAuxiliaryError d δ D (sieveParameter D (growingPrefixIndex d D + 1)) H →
      0 ≤ H (sieveParameter D (growingPrefixIndex d D + 1)) →
      rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        (sieveProduct P primeDensity (growingPrefixIndex d D + 1) / sieveProduct P primeDensity (z + 1)) *
          Real.exp (-growingSieveParameter d (Real.log D)) * inflatedAuxiliaryError d δ D
            (sieveParameter D (growingPrefixIndex d D + 1)) H := by
    intro H hbound hH
    have hE := inflatedAuxiliaryError_nonneg d δ D _ H hD (by linarith) hH
    have htail := hbound.trans (mul_le_mul_of_nonneg_right he hE)
    calc
      _ ≤ (sieveProduct P primeDensity (growingPrefixIndex d D + 1) /
          sieveProduct P primeDensity (z + 1)) * rosserRelativeDefect P (growingPrefixIndex d D + 1) upper D := hprefix
      _ ≤ (sieveProduct P primeDensity (growingPrefixIndex d D + 1) /
          sieveProduct P primeDensity (z + 1)) *
            (Real.exp (-growingSieveParameter d (Real.log D)) *
              inflatedAuxiliaryError d δ D (sieveParameter D (growingPrefixIndex d D + 1)) H) :=
        mul_le_mul_of_nonneg_left htail hratio
      _ = _ := by ring
  exact ⟨hstep upperAuxiliaryError hsmall.1 (upperAuxiliaryError_nonneg _ (by linarith)),
    hstep lowerAuxiliaryError hsmall.2 (lowerAuxiliaryError_nonneg _ (by linarith))⟩

/-- The product ratio is absorbed into a fixed dimension-one constant.
The bound is uniform in the cumulative depth and the prime set. -/
theorem rosserPartialPrefix_growing_uniform_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ d δ : ℝ, 2 < d → ∀ᶠ D in atTop,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ N z : ℕ, growingPrefixIndex d D ≤ z → ∀ upper : Bool,
      rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        ((4 * (1 + K / Real.log 2)) * growingSieveParameter d (Real.log D) / sieveParameter D (z + 1)) *
          Real.exp (-growingSieveParameter d (Real.log D)) * inflatedAuxiliaryError d δ D
            (sieveParameter D (growingPrefixIndex d D + 1)) upperAuxiliaryError ∧
      rosserPartialPrefix P N z upper D (growingPrefixIndex d D) ≤
        ((4 * (1 + K / Real.log 2)) * growingSieveParameter d (Real.log D) / sieveParameter D (z + 1)) *
          Real.exp (-growingSieveParameter d (Real.log D)) * inflatedAuxiliaryError d δ D
            (sieveParameter D (growingPrefixIndex d D + 1)) lowerAuxiliaryError := by
  obtain ⟨K, hK, hratio⟩ := growingPrefix_product_ratio_bound
  refine ⟨K, hK, ?_⟩
  intro d δ hd
  have hg := (tendsto_growingSieveParameter_atTop d (by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [rosserPartialPrefix_growing_bound d δ hd,
    eventually_growingPrefixCutoff_properties d (by linarith), hg.eventually_ge_atTop 6] with D hp hc hσ
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  dsimp only [Function.comp_def] at hσ
  intro P hP hodd N z hmz upper
  have h := hp P hP hodd N z upper
  have hr := hratio d D hD hL hw z hmz P hP hodd
  have hs : 6 ≤ sieveParameter D (growingPrefixIndex d D + 1) := hσ.trans hlo
  have hu := inflatedAuxiliaryError_nonneg d δ D (sieveParameter D (growingPrefixIndex d D + 1)) upperAuxiliaryError hD (by linarith)
    (upperAuxiliaryError_nonneg _ (by linarith))
  have hl := inflatedAuxiliaryError_nonneg d δ D (sieveParameter D (growingPrefixIndex d D + 1)) lowerAuxiliaryError hD (by linarith)
    (lowerAuxiliaryError_nonneg _ (by linarith))
  have he := mul_le_mul_of_nonneg_right hr (Real.exp_pos (-growingSieveParameter d (Real.log D))).le
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right he hu), h.2.trans (mul_le_mul_of_nonneg_right he hl)⟩

end Chen.LinearSieve
