import Submission.ChenTheorem.Lemma9.LinearSieve.InflatedTerminalAbsorption

set_option autoImplicit true
open Filter

namespace Chen.LinearSieve

/-- The terminal density loss is absorbed, leaving a quantitative strict
contraction for the true child errors above the growing prefix. -/
theorem weighted_buchstab_inflated_absorbed_lower (d δ : ℝ) (hd : 3 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, growingPrefixCutoff d D ≤ z → 3 ≤ sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∑ p ∈ Finset.Ioc (growingPrefixIndex d D) z,
        inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError * buchstabCoefficient P z p) ≤
      (1 - (1 - δ) / (16 * growingSieveParameter d (Real.log D))) *
        inflatedAuxiliaryError d δ D (sieveParameter D z) upperAuxiliaryError := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_inflated_contracted_lower
  filter_upwards [hb d δ (by linarith) hδ hδ1,
    eventually_inflatedTerminalLower_small d δ K ((1 - δ) / 8) hd hδ1.le hK.le (by linarith),
    eventually_growingPrefixCutoff_properties d (by linarith)] with D hsum hterminal hc
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  intro z hwz hs P hP hodd
  have hσ := (growingSieveParameter_pos d (Real.log D) hL).ne'
  have hparam := sieveParameter_growingPrefixCutoff d D hL
  have hsB := (sieveParameter_mem_Icc hD hw
    (show (z : ℝ) ∈ Set.Icc (growingPrefixCutoff d D) z from ⟨hwz, le_rfl⟩)).2
  rw [hparam] at hsB
  have h := hsum (growingPrefixCutoff d D) (2 * growingSieveParameter d (Real.log D)) z hw hwz hs
    hparam.le le_rfl P hP hodd
  have he := hterminal (sieveParameter D z) hs hsB
  have hcEq : (1 - (1 - δ) / (4 * (2 * growingSieveParameter d (Real.log D)))) +
      ((1 - δ) / 8) / (2 * growingSieveParameter d (Real.log D)) =
      1 - (1 - δ) / (16 * growingSieveParameter d (Real.log D)) := by field_simp; ring
  have hfinal := h.trans (_root_.add_le_add le_rfl he)
  rw [← add_mul, hcEq] at hfinal
  simpa only [growingPrefixIndex] using hfinal

theorem weighted_buchstab_inflated_absorbed_upper (d δ : ℝ) (hd : 3 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, growingPrefixCutoff d D ≤ z → 2 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∑ p ∈ Finset.Ioc (growingPrefixIndex d D) z,
        inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError * buchstabCoefficient P z p) ≤
      (1 - (1 - δ) / (16 * growingSieveParameter d (Real.log D))) *
        inflatedAuxiliaryError d δ D (sieveParameter D z) lowerAuxiliaryError := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_inflated_contracted_upper
  filter_upwards [hb d δ (by linarith) hδ hδ1,
    eventually_inflatedTerminalUpper_small d δ K ((1 - δ) / 8) hd hδ1.le hK.le (by linarith),
    eventually_growingPrefixCutoff_properties d (by linarith)] with D hsum hterminal hc
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  intro z hwz hs P hP hodd
  have hσ := (growingSieveParameter_pos d (Real.log D) hL).ne'
  have hparam := sieveParameter_growingPrefixCutoff d D hL
  have hsB := (sieveParameter_mem_Icc hD hw
    (show (z : ℝ) ∈ Set.Icc (growingPrefixCutoff d D) z from ⟨hwz, le_rfl⟩)).2
  rw [hparam] at hsB
  have h := hsum (growingPrefixCutoff d D) (2 * growingSieveParameter d (Real.log D)) z hw hwz hs
    hparam.le le_rfl P hP hodd
  have he := hterminal (sieveParameter D z) hs hsB
  have hcEq : (1 - (1 - δ) / (4 * (2 * growingSieveParameter d (Real.log D)))) +
      ((1 - δ) / 8) / (2 * growingSieveParameter d (Real.log D)) =
      1 - (1 - δ) / (16 * growingSieveParameter d (Real.log D)) := by field_simp; ring
  have hfinal := h.trans (_root_.add_le_add le_rfl he)
  rw [← add_mul, hcEq] at hfinal
  simpa only [growingPrefixIndex] using hfinal

end Chen.LinearSieve
