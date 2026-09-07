import Submission.ChenTheorem.Lemma9.LinearSieve.BuchstabErrors
import Submission.ChenTheorem.Lemma9.LinearSieve.RosserPartialDefect
import Submission.ChenTheorem.Lemma9.LinearSieve.InflatedAbsorbedChildSum
import Submission.ChenTheorem.Lemma9.LinearSieve.ContinuousTerminalAbsorption

set_option autoImplicit true
open Filter Finset

namespace Chen.LinearSieve

/-- The active cumulative-depth step against the full convergent error, with both density losses absorbed.
The threshold is uniform in the cumulative depth and multiplier. The actual small-prime
prefix and the child induction hypothesis are retained explicitly. -/
theorem rosserPartialDefect_fullError_upper_step (d δ : ℝ) (hd : 3 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hgap : 3 / d < 1 - δ) :
    ∀ᶠ D : ℝ in atTop, ∀ R : ℕ, ∀ M : ℝ, 1 ≤ M → ∀ z : ℕ,
      growingPrefixCutoff d D ≤ z → 3 ≤ sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (¬(true = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2)) →
      (∀ p ∈ Ioc (growingPrefixIndex d D) z, p ∈ P →
        rosserPartialDefect P R p false (D / p) ≤
          lowerContinuousError (sieveParameter D p - 1) +
          M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError) →
      rosserPartialDefect P (R + 1) (z + 1) true D ≤
        rosserPartialPrefix P R z true D (growingPrefixIndex d D) +
        upperContinuousError (sieveParameter D z) +
        M * ((1 - (1 - δ) / (32 * growingSieveParameter d (Real.log D))) *
          inflatedAuxiliaryError d δ D (sieveParameter D z) upperAuxiliaryError) := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_lowerContinuousError_auxiliary
  filter_upwards [weighted_buchstab_inflated_absorbed_lower d δ hd hδ hδ1,
    eventually_continuousTerminalLower_small d δ K ((1 - δ) / 16)
      hd hgap hK.le (by linarith),
    eventually_growingPrefixCutoff_properties d (by linarith)] with D hsum hterminal hc
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  intro R M hM z hwz hs P hP hodd hactive hchild
  have hM0 : 0 ≤ M := by linarith
  have hmz : growingPrefixIndex d D ≤ z :=
    (Nat.floor_le_floor hwz).trans_eq (Nat.floor_natCast z)
  have h := rosserPartialDefect_step_of_child_bound P hP hodd R z
    (growingPrefixIndex d D) hmz true D
    (fun p => lowerContinuousError (sieveParameter D p - 1))
    (fun p => M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError)
    hactive hchild
  have hscale : (∑ p ∈ Ioc (growingPrefixIndex d D) z,
      (M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError) *
        buchstabCoefficient P z p) =
      M * ∑ p ∈ Ioc (growingPrefixIndex d D) z,
        inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError *
          buchstabCoefficient P z p := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  rw [hscale] at h
  have hparam := sieveParameter_growingPrefixCutoff d D hL
  have hsB := (sieveParameter_mem_Icc hD hw
    (show (z : ℝ) ∈ Set.Icc (growingPrefixCutoff d D) z from ⟨hwz, le_rfl⟩)).2
  rw [hparam] at hsB
  have hb' := hb D (growingPrefixCutoff d D) z hD hw hwz hs P hP hodd
  have ht := hterminal (sieveParameter D z) hs hsB
  have he := mul_le_mul_of_nonneg_left (hsum z hwz hs P hP hodd) hM0
  have hE := inflatedAuxiliaryError_nonneg d δ D (sieveParameter D z)
    upperAuxiliaryError hD (by linarith) (upperAuxiliaryError_nonneg _ (by linarith))
  have hσ := growingSieveParameter_pos d (Real.log D) hL
  have hsmall : 0 ≤ (((1 - δ) / 16) / (2 * growingSieveParameter d (Real.log D))) *
      inflatedAuxiliaryError d δ D (sieveParameter D z) upperAuxiliaryError :=
    mul_nonneg (div_nonneg (by linarith) (by positivity)) hE
  have htM := ht.trans (le_mul_of_one_le_left hsmall hM)
  have hbM := hb'.trans (_root_.add_le_add le_rfl htM)
  have hfinal := h.trans (_root_.add_le_add (_root_.add_le_add le_rfl hbM) he)
  have hcEq : (((1 - δ) / 16) / (2 * growingSieveParameter d (Real.log D))) +
      (1 - (1 - δ) / (16 * growingSieveParameter d (Real.log D))) =
      1 - (1 - δ) / (32 * growingSieveParameter d (Real.log D)) := by
    field_simp
    ring
  calc
    _ ≤ _ := hfinal
    _ = _ := by rw [← hcEq]; ring

/-- The active cumulative-depth step against the full convergent error, with both density losses absorbed.
The threshold is uniform in the cumulative depth and multiplier. The actual small-prime
prefix and the child induction hypothesis are retained explicitly. -/
theorem rosserPartialDefect_fullError_lower_step (d δ : ℝ) (hd : 3 < d)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hgap : 3 / d < 1 - δ) :
    ∀ᶠ D : ℝ in atTop, ∀ R : ℕ, ∀ M : ℝ, 1 ≤ M → ∀ z : ℕ,
      growingPrefixCutoff d D ≤ z → 2 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (¬(false = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2)) →
      (∀ p ∈ Ioc (growingPrefixIndex d D) z, p ∈ P →
        rosserPartialDefect P R p true (D / p) ≤
          upperContinuousError (sieveParameter D p - 1) +
          M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError) →
      rosserPartialDefect P (R + 1) (z + 1) false D ≤
        rosserPartialPrefix P R z false D (growingPrefixIndex d D) +
        lowerContinuousError (sieveParameter D z) +
        M * ((1 - (1 - δ) / (32 * growingSieveParameter d (Real.log D))) *
          inflatedAuxiliaryError d δ D (sieveParameter D z) lowerAuxiliaryError) := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_upperContinuousError_auxiliary
  filter_upwards [weighted_buchstab_inflated_absorbed_upper d δ hd hδ hδ1,
    eventually_continuousTerminalUpper_small d δ K ((1 - δ) / 16)
      hd hgap hK.le (by linarith),
    eventually_growingPrefixCutoff_properties d (by linarith)] with D hsum hterminal hc
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  intro R M hM z hwz hs P hP hodd hactive hchild
  have hM0 : 0 ≤ M := by linarith
  have hmz : growingPrefixIndex d D ≤ z :=
    (Nat.floor_le_floor hwz).trans_eq (Nat.floor_natCast z)
  have h := rosserPartialDefect_step_of_child_bound P hP hodd R z
    (growingPrefixIndex d D) hmz false D
    (fun p => upperContinuousError (sieveParameter D p - 1))
    (fun p => M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError)
    hactive hchild
  have hscale : (∑ p ∈ Ioc (growingPrefixIndex d D) z,
      (M * inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError) *
        buchstabCoefficient P z p) =
      M * ∑ p ∈ Ioc (growingPrefixIndex d D) z,
        inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError *
          buchstabCoefficient P z p := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  rw [hscale] at h
  have hparam := sieveParameter_growingPrefixCutoff d D hL
  have hsB := (sieveParameter_mem_Icc hD hw
    (show (z : ℝ) ∈ Set.Icc (growingPrefixCutoff d D) z from ⟨hwz, le_rfl⟩)).2
  rw [hparam] at hsB
  have hb' := hb D (growingPrefixCutoff d D) z hD hw hwz hs P hP hodd
  have ht := hterminal (sieveParameter D z) hs hsB
  have he := mul_le_mul_of_nonneg_left (hsum z hwz hs P hP hodd) hM0
  have hE := inflatedAuxiliaryError_nonneg d δ D (sieveParameter D z)
    lowerAuxiliaryError hD (by linarith) (lowerAuxiliaryError_nonneg _ (by linarith))
  have hσ := growingSieveParameter_pos d (Real.log D) hL
  have hsmall : 0 ≤ (((1 - δ) / 16) / (2 * growingSieveParameter d (Real.log D))) *
      inflatedAuxiliaryError d δ D (sieveParameter D z) lowerAuxiliaryError :=
    mul_nonneg (div_nonneg (by linarith) (by positivity)) hE
  have htM := ht.trans (le_mul_of_one_le_left hsmall hM)
  have hbM := hb'.trans (_root_.add_le_add le_rfl htM)
  have hfinal := h.trans (_root_.add_le_add (_root_.add_le_add le_rfl hbM) he)
  have hcEq : (((1 - δ) / 16) / (2 * growingSieveParameter d (Real.log D))) +
      (1 - (1 - δ) / (16 * growingSieveParameter d (Real.log D))) =
      1 - (1 - δ) / (32 * growingSieveParameter d (Real.log D)) := by
    field_simp
    ring
  calc
    _ ≤ _ := hfinal
    _ = _ := by rw [← hcEq]; ring

end Chen.LinearSieve
