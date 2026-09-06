import ChenTheorem.Lemma9.LinearSieve.RosserPartialDefect

open Finset

namespace Chen.LinearSieve

/-- A cumulative depth step. Both the small-prime prefix and the two
density errors remain explicit, as does the child induction hypothesis. -/
theorem rosserPartialDefect_upper_step :
    ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ ∀ R N : ℕ, ∀ δ D w M : ℝ, ∀ z : ℕ,
      0 ≤ δ → δ ≤ 1 → 0 ≤ M → 1 < D → 2 ≤ w → w ≤ z →
      3 ≤ sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (¬(true = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2)) →
      (∀ p ∈ Ioc ⌊w⌋₊ z, p ∈ P →
        rosserPartialDefect P R p false (D / p) ≤
          lowerContinuousPartial N (sieveParameter D p - 1) +
          M * auxiliaryErrorScale δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError) →
      rosserPartialDefect P (R + 1) (z + 1) true D ≤
        rosserPartialPrefix P R z true D ⌊w⌋₊ +
        upperContinuousPartial N (sieveParameter D z) +
        M * auxiliaryErrorScale δ D (sieveParameter D z) upperAuxiliaryError +
        2 * K₁ * ((sieveParameter D z - 1) * lowerAuxiliaryError (sieveParameter D z - 1)) /
          Real.log w +
        2 * K₂ * M * auxiliaryErrorScale δ (D / z) (sieveParameter (D / z) z) lowerAuxiliaryError /
          Real.log w := by
  obtain ⟨K₁, hK₁, hb⟩ := weighted_buchstab_lowerContinuousPartial_auxiliary
  obtain ⟨K₂, hK₂, he⟩ := weighted_buchstab_auxiliary_level_lower
  refine ⟨K₁, K₂, hK₁, hK₂, ?_⟩
  intro R N δ D w M z hδ hδ1 hM hD hw hwz hs P hP hodd hactive hchild
  have hmz : ⌊w⌋₊ ≤ z := (Nat.floor_le_floor hwz).trans_eq (Nat.floor_natCast z)
  have h := rosserPartialDefect_step_of_child_bound P hP hodd R z ⌊w⌋₊ hmz true D
    (fun p => lowerContinuousPartial N (sieveParameter D p - 1))
    (fun p => M * auxiliaryErrorScale δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError)
    hactive hchild
  have hsum : (∑ p ∈ Ioc ⌊w⌋₊ z,
      (M * auxiliaryErrorScale δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError) *
        buchstabCoefficient P z p) =
      M * ∑ p ∈ Ioc ⌊w⌋₊ z,
        auxiliaryErrorScale δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError *
          buchstabCoefficient P z p := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  rw [hsum] at h
  have hb' := hb N D w z hD hw hwz hs P hP hodd
  have he' := mul_le_mul_of_nonneg_left (he δ D w z hδ hδ1 hD hw hwz hs P hP hodd) hM
  have ht := h.trans (_root_.add_le_add (_root_.add_le_add le_rfl hb') he')
  convert! ht using 1
  ring

/-- A cumulative depth step. Both the small-prime prefix and the two
density errors remain explicit, as does the child induction hypothesis. -/
theorem rosserPartialDefect_lower_step :
    ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ ∀ R N : ℕ, ∀ δ D w M : ℝ, ∀ z : ℕ,
      0 ≤ δ → δ ≤ 1 → 0 ≤ M → 1 < D → 2 ≤ w → w ≤ z →
      2 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (¬(false = false ∧ D ≤ ((z + 1 : ℕ) : ℝ) ^ 2)) →
      (∀ p ∈ Ioc ⌊w⌋₊ z, p ∈ P →
        rosserPartialDefect P R p true (D / p) ≤
          upperContinuousPartial N (sieveParameter D p - 1) +
          M * auxiliaryErrorScale δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError) →
      rosserPartialDefect P (R + 1) (z + 1) false D ≤
        rosserPartialPrefix P R z false D ⌊w⌋₊ +
        lowerContinuousPartial (N + 1) (sieveParameter D z) +
        M * auxiliaryErrorScale δ D (sieveParameter D z) lowerAuxiliaryError +
        2 * K₁ * ((sieveParameter D z - 1) * upperAuxiliaryError (sieveParameter D z - 1)) /
          Real.log w +
        2 * K₂ * M * auxiliaryErrorScale δ (D / z) (sieveParameter (D / z) z) upperAuxiliaryError /
          Real.log w := by
  obtain ⟨K₁, hK₁, hb⟩ := weighted_buchstab_upperContinuousPartial_auxiliary
  obtain ⟨K₂, hK₂, he⟩ := weighted_buchstab_auxiliary_level_upper
  refine ⟨K₁, K₂, hK₁, hK₂, ?_⟩
  intro R N δ D w M z hδ hδ1 hM hD hw hwz hs P hP hodd hactive hchild
  have hmz : ⌊w⌋₊ ≤ z := (Nat.floor_le_floor hwz).trans_eq (Nat.floor_natCast z)
  have h := rosserPartialDefect_step_of_child_bound P hP hodd R z ⌊w⌋₊ hmz false D
    (fun p => upperContinuousPartial N (sieveParameter D p - 1))
    (fun p => M * auxiliaryErrorScale δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError)
    hactive hchild
  have hsum : (∑ p ∈ Ioc ⌊w⌋₊ z,
      (M * auxiliaryErrorScale δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError) *
        buchstabCoefficient P z p) =
      M * ∑ p ∈ Ioc ⌊w⌋₊ z,
        auxiliaryErrorScale δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError *
          buchstabCoefficient P z p := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  rw [hsum] at h
  have hb' := hb N D w z hD hw hwz hs P hP hodd
  have he' := mul_le_mul_of_nonneg_left (he δ D w z hδ hδ1 hD hw hwz hs P hP hodd) hM
  have ht := h.trans (_root_.add_le_add (_root_.add_le_add le_rfl hb') he')
  convert! ht using 1
  ring

end Chen.LinearSieve
