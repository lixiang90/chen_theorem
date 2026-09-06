import ChenTheorem.Lemma9.LinearSieve.RosserFullErrorStep
import ChenTheorem.Lemma9.LinearSieve.RosserPrefixAbsorption

open Filter Finset

namespace Chen.LinearSieve

/-- All prefix and density losses are absorbed at the actual parent cutoff
`z + 1`. This is a conditional active step against the full convergent errors, uniform in depth. -/
theorem rosserPartialDefect_fullError_upper_parent_step (d δ : ℝ) (hd : 3 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hgap : 3 / d < 1 - δ) :
    ∀ᶠ D : ℝ in atTop, ∀ R : ℕ, ∀ M : ℝ, 1 ≤ M → ∀ z : ℕ,
      growingPrefixCutoff d D ≤ z → 3 ≤ sieveParameter D (z + 1) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (¬(true = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2)) →
      (∀ p ∈ Ioc (growingPrefixIndex d D) z, p ∈ P →
        rosserPartialDefect P R p false (D / p) ≤
          lowerContinuousError (sieveParameter D p - 1) +
          M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError) →
      rosserPartialDefect P (R + 1) (z + 1) true D ≤
        upperContinuousError (sieveParameter D (z + 1)) +
        M * ((1 - (1 - δ) / (64 * growingSieveParameter d (Real.log D))) *
          inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) upperAuxiliaryError) := by
  have hg := (tendsto_growingSieveParameter_atTop d (by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [rosserPartialDefect_fullError_upper_step d δ hd hδ hδ1 hgap,
    rosserPartialPrefix_parent_inverse_small d δ ((1 - δ) / 64) (by linarith) (by linarith),
    eventually_inflatedAuxiliaryError_transport d δ (by linarith),
    eventually_growingPrefixCutoff_properties d (by linarith), hg.eventually_ge_atTop 1]
      with D hstep hpref htrans hc hσ1
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  dsimp only [Function.comp_def] at hσ1
  intro R M hM z hwz hs P hP hodd hactive hchild
  have hz : 1 < (z : ℝ) := by linarith
  have hst : sieveParameter D (z + 1) ≤ sieveParameter D z :=
    sieveParameter_antitone hD hz (show 1 < (z : ℝ) + 1 by linarith) (by linarith)
  have hsz : 3 ≤ sieveParameter D z := hs.trans hst
  have hmz : growingPrefixIndex d D ≤ z :=
    (Nat.floor_le_floor hwz).trans_eq (Nat.floor_natCast z)
  have h := hstep R M hM z hwz hsz P hP hodd hactive hchild
  have hp := (hpref P hP hodd R z hmz hs true).1
  have hsB := (sieveParameter_mem_Icc hD hw
    (show (z : ℝ) ∈ Set.Icc (growingPrefixCutoff d D) z from ⟨hwz, le_rfl⟩)).2
  rw [sieveParameter_growingPrefixCutoff d D hL] at hsB
  have ht := (htrans.2 _ _ hs hst hsB).1
  have hE := inflatedAuxiliaryError_nonneg d δ D (sieveParameter D (z + 1))
    upperAuxiliaryError hD (by linarith) (upperAuxiliaryError_nonneg _ (by linarith))
  have hr : sieveParameter D (z + 1) / sieveParameter D z ≤ 1 :=
    (div_le_one (by linarith : 0 < sieveParameter D z)).mpr hst
  have hEt := ht.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr hE)
  have hσ : 0 < growingSieveParameter d (Real.log D) := by linarith
  have hcoef : 0 ≤ 1 - (1 - δ) / (32 * growingSieveParameter d (Real.log D)) := by
    have hdiv : (1 - δ) / (32 * growingSieveParameter d (Real.log D)) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have he := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEt hcoef) (by linarith : 0 ≤ M)
  have hmain := antitoneOn_upperContinuousError
    (show 1 < sieveParameter D (z + 1) by linarith)
    (show 1 < sieveParameter D z by linarith) hst
  have hsmall : 0 ≤ (((1 - δ) / 64) / growingSieveParameter d (Real.log D)) *
      inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) upperAuxiliaryError :=
    mul_nonneg (div_nonneg (by linarith) hσ.le) hE
  have hpM := hp.trans (le_mul_of_one_le_left hsmall hM)
  have hfinal := h.trans (_root_.add_le_add (_root_.add_le_add hpM hmain) he)
  have hcEq : (((1 - δ) / 64) / growingSieveParameter d (Real.log D)) +
      (1 - (1 - δ) / (32 * growingSieveParameter d (Real.log D))) =
      1 - (1 - δ) / (64 * growingSieveParameter d (Real.log D)) := by
    field_simp
    ring
  calc
    _ ≤ _ := hfinal
    _ = _ := by rw [← hcEq]; ring

/-- All prefix and density losses are absorbed at the actual parent cutoff
`z + 1`. This is a conditional active step against the full convergent errors, uniform in depth. -/
theorem rosserPartialDefect_fullError_lower_parent_step (d δ : ℝ) (hd : 3 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hgap : 3 / d < 1 - δ) :
    ∀ᶠ D : ℝ in atTop, ∀ R : ℕ, ∀ M : ℝ, 1 ≤ M → ∀ z : ℕ,
      growingPrefixCutoff d D ≤ z → 2 < sieveParameter D (z + 1) →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (¬(false = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2)) →
      (∀ p ∈ Ioc (growingPrefixIndex d D) z, p ∈ P →
        rosserPartialDefect P R p true (D / p) ≤
          upperContinuousError (sieveParameter D p - 1) +
          M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError) →
      rosserPartialDefect P (R + 1) (z + 1) false D ≤
        lowerContinuousError (sieveParameter D (z + 1)) +
        M * ((1 - (1 - δ) / (64 * growingSieveParameter d (Real.log D))) *
          inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError) := by
  have hg := (tendsto_growingSieveParameter_atTop d (by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [rosserPartialDefect_fullError_lower_step d δ hd hδ hδ1 hgap,
    rosserPartialPrefix_lower_parent_inverse_small d δ ((1 - δ) / 64) (by linarith) (by linarith),
    eventually_inflatedLowerAuxiliaryError_transport d δ (by linarith),
    eventually_growingPrefixCutoff_properties d (by linarith), hg.eventually_ge_atTop 1]
      with D hstep hpref htrans hc hσ1
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  dsimp only [Function.comp_def] at hσ1
  intro R M hM z hwz hs P hP hodd hactive hchild
  have hz : 1 < (z : ℝ) := by linarith
  have hst : sieveParameter D (z + 1) ≤ sieveParameter D z :=
    sieveParameter_antitone hD hz (show 1 < (z : ℝ) + 1 by linarith) (by linarith)
  have hsz : 2 < sieveParameter D z := hs.trans_le hst
  have hmz : growingPrefixIndex d D ≤ z :=
    (Nat.floor_le_floor hwz).trans_eq (Nat.floor_natCast z)
  have h := hstep R M hM z hwz hsz P hP hodd hactive hchild
  have hp := hpref P hP hodd R z hmz hs.le false
  have hsB := (sieveParameter_mem_Icc hD hw
    (show (z : ℝ) ∈ Set.Icc (growingPrefixCutoff d D) z from ⟨hwz, le_rfl⟩)).2
  rw [sieveParameter_growingPrefixCutoff d D hL] at hsB
  have ht := htrans.2 _ _ hs.le hst hsB
  have hE := inflatedAuxiliaryError_nonneg d δ D (sieveParameter D (z + 1))
    lowerAuxiliaryError hD (by linarith) (lowerAuxiliaryError_nonneg _ (by linarith))
  have hr : sieveParameter D (z + 1) / sieveParameter D z ≤ 1 :=
    (div_le_one (by linarith : 0 < sieveParameter D z)).mpr hst
  have hEt := ht.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr hE)
  have hσ : 0 < growingSieveParameter d (Real.log D) := by linarith
  have hcoef : 0 ≤ 1 - (1 - δ) / (32 * growingSieveParameter d (Real.log D)) := by
    have hdiv : (1 - δ) / (32 * growingSieveParameter d (Real.log D)) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have he := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEt hcoef) (by linarith : 0 ≤ M)
  have hmain := antitoneOn_lowerContinuousError hs.le hsz.le hst
  have hsmall : 0 ≤ (((1 - δ) / 64) / growingSieveParameter d (Real.log D)) *
      inflatedAuxiliaryError d δ D (sieveParameter D (z + 1)) lowerAuxiliaryError :=
    mul_nonneg (div_nonneg (by linarith) hσ.le) hE
  have hpM := hp.trans (le_mul_of_one_le_left hsmall hM)
  have hfinal := h.trans (_root_.add_le_add (_root_.add_le_add hpM hmain) he)
  have hcEq : (((1 - δ) / 64) / growingSieveParameter d (Real.log D)) +
      (1 - (1 - δ) / (32 * growingSieveParameter d (Real.log D))) =
      1 - (1 - δ) / (64 * growingSieveParameter d (Real.log D)) := by
    field_simp
    ring
  calc
    _ ≤ _ := hfinal
    _ = _ := by rw [← hcEq]; ring

end Chen.LinearSieve
