import ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryContraction

open Set MeasureTheory Filter

namespace Chen.LinearSieve

theorem scaled_inflatedIntegral_le_parent (d δ D s b ρ : ℝ) (H J : ℝ → ℝ)
    (hD : 1 < D) (hs : 0 < s) (hsb : s ≤ b) (hρ : 0 ≤ ρ) (hHb : 0 ≤ H b)
    (hi : (∫ t in s..b, inflatedChildAuxiliaryWeight d δ D t J) ≤
      ρ * (auxiliaryInflation d D s * (s ^ 2 * H s) - auxiliaryInflation d D b * (b ^ 2 * H b))) :
    (Real.log D) ^ (-δ) * ((1 / s) * (∫ t in Ioc s b, inflatedChildAuxiliaryWeight d δ D t J)) ≤
      ρ * inflatedAuxiliaryError d δ D s H := by
  have hn : 0 ≤ auxiliaryInflation d D b * (b ^ 2 * H b) :=
    mul_nonneg (auxiliaryInflation_pos d D b hD (hs.le.trans hsb)).le (mul_nonneg (sq_nonneg _) hHb)
  have hp := hi.trans (mul_le_mul_of_nonneg_left (sub_le_self _ hn) hρ)
  have hm := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (Real.rpow_nonneg (Real.log_pos hD).le (-δ)) (one_div_nonneg.mpr hs.le))
  rw [intervalIntegral.integral_of_le hsb] at hm
  convert! hm using 1
  · ring
  · unfold inflatedAuxiliaryError auxiliaryErrorScale
    field_simp

/-- The upper sieve's true child-error sum has a strictly contracted parent
term. The remaining terminal density loss stays explicit. -/
theorem weighted_buchstab_inflated_contracted_lower :
    ∃ K : ℝ, 0 < K ∧ ∀ d δ : ℝ, 1 ≤ d → 0 ≤ δ → δ < 1 → ∀ᶠ D in atTop,
      ∀ w B : ℝ, ∀ z : ℕ, 2 ≤ w → w ≤ z → 3 ≤ sieveParameter D z →
      sieveParameter D w ≤ B → B ≤ 2 * growingSieveParameter d (Real.log D) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
        inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError * buchstabCoefficient P z p) ≤
        (1 - (1 - δ) / (4 * B)) * inflatedAuxiliaryError d δ D (sieveParameter D z) upperAuxiliaryError +
        (Real.log D) ^ (-δ) * (2 * K * inflatedChildAuxiliaryWeight d δ D (sieveParameter D z) lowerAuxiliaryError / Real.log w) := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_inflated_level_lower
  refine ⟨K, hK, ?_⟩
  intro d δ hd hδ hδ1
  filter_upwards [hb d δ hd (by linarith),
    eventually_integral_inflatedChildLower_contraction d δ (by linarith) hδ hδ1] with D hsum hC
  intro w B z hw hwz hs hbB hcut P hP hodd
  have hsb := (sieveParameter_mem_Icc hC.1 hw (show (z : ℝ) ∈ Icc w z from ⟨hwz, le_rfl⟩)).2
  have hρ : 0 ≤ 1 - (1 - δ) / (4 * B) := by
    have hB : 3 ≤ B := hs.trans (hsb.trans hbB)
    have h := (div_le_one (show 0 < 4 * B by linarith)).mpr (show 1 - δ ≤ 4 * B by linarith)
    linarith
  have hi := scaled_inflatedIntegral_le_parent d δ D _ _ _ upperAuxiliaryError lowerAuxiliaryError hC.1
    (by linarith) hsb hρ (upperAuxiliaryError_nonneg _ (by linarith))
    (hC.2 _ _ B hs hsb hbB hcut)
  have h := hsum w z hw hwz hs (by linarith [hbB.trans hcut]) P hP hodd
  nlinarith

theorem weighted_buchstab_inflated_contracted_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ d δ : ℝ, 1 ≤ d → 0 ≤ δ → δ < 1 → ∀ᶠ D in atTop,
      ∀ w B : ℝ, ∀ z : ℕ, 2 ≤ w → w ≤ z → 2 < sieveParameter D z →
      sieveParameter D w ≤ B → B ≤ 2 * growingSieveParameter d (Real.log D) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
        inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError * buchstabCoefficient P z p) ≤
        (1 - (1 - δ) / (4 * B)) * inflatedAuxiliaryError d δ D (sieveParameter D z) lowerAuxiliaryError +
        (Real.log D) ^ (-δ) * (2 * K * inflatedChildAuxiliaryWeight d δ D (sieveParameter D z) upperAuxiliaryError / Real.log w) := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_inflated_level_upper
  refine ⟨K, hK, ?_⟩
  intro d δ hd hδ hδ1
  filter_upwards [hb d δ hd (by linarith),
    eventually_integral_inflatedChildUpper_contraction d δ (by linarith) hδ hδ1] with D hsum hC
  intro w B z hw hwz hs hbB hcut P hP hodd
  have hsb := (sieveParameter_mem_Icc hC.1 hw (show (z : ℝ) ∈ Icc w z from ⟨hwz, le_rfl⟩)).2
  have hρ : 0 ≤ 1 - (1 - δ) / (4 * B) := by
    have hB : 2 < B := hs.trans_le (hsb.trans hbB)
    have h := (div_le_one (show 0 < 4 * B by linarith)).mpr (show 1 - δ ≤ 4 * B by linarith)
    linarith
  have hi := scaled_inflatedIntegral_le_parent d δ D _ _ _ lowerAuxiliaryError upperAuxiliaryError hC.1
    (by linarith) hsb hρ (lowerAuxiliaryError_nonneg _ (by linarith))
    (hC.2 _ _ B hs hsb hbB hcut)
  have h := hsum w z hw hwz hs (by linarith [hbB.trans hcut]) P hP hodd
  nlinarith

end Chen.LinearSieve
