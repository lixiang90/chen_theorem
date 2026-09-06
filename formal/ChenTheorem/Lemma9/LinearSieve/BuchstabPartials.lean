import ChenTheorem.Lemma9.LinearSieve.AuxiliaryMajorant
import ChenTheorem.Lemma9.LinearSieve.BuchstabFirstTerm

open Finset Set

namespace Chen.LinearSieve

theorem upperContinuousPartial_eq_tail (N : ℕ) (s : ℝ) (hs : 3 ≤ s) :
    upperContinuousPartial N s = ∑ k ∈ range N, rosserContinuousTerm (2 * k + 3) s := by
  rw [upperContinuousPartial, sum_range_succ']
  have hf : rosserContinuousTerm 1 s = 0 := rosserContinuousTerm_eq_zero 1 s (by norm_num; exact hs)
  simp only [mul_zero, zero_add, hf, add_zero]
  apply sum_congr rfl
  intro k _
  congr 1

theorem weighted_buchstab_upperContinuousPartial :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∀ D w : ℝ, ∀ z : ℕ,
      1 < D → 2 ≤ w → w ≤ z → 2 ≤ sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
          upperContinuousPartial N (sieveParameter D p - 1) * buchstabCoefficient P z p) ≤
        lowerContinuousPartial (N + 1) (sieveParameter D z) +
          2 * K * upperContinuousPartial N (sieveParameter D z - 1) / Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_allContinuousTerms_bound
  refine ⟨K, hK, ?_⟩
  intro N D w z hD hw hwz hs P hP hodd
  calc
    _ = ∑ k ∈ range (N + 1), ∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
        rosserContinuousTerm (2 * k + 1) (sieveParameter D p - 1) * buchstabCoefficient P z p := by
      simp only [upperContinuousPartial, sum_mul]
      rw [sum_comm]
    _ ≤ ∑ k ∈ range (N + 1), (rosserContinuousTerm (2 * k + 2) (sieveParameter D z) +
        2 * K * rosserContinuousTerm (2 * k + 1) (sieveParameter D z - 1) / Real.log w) := by
      apply sum_le_sum
      intro k _
      apply hb (2 * k) D w z hD hw hwz _ P hP hodd
      simpa [rosserContinuousCutoff, Nat.even_add, Nat.even_mul] using hs
    _ = _ := by
      simp only [sum_add_distrib, lowerContinuousPartial, upperContinuousPartial,
        ← sum_div, ← mul_sum]

theorem weighted_buchstab_lowerContinuousPartial :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∀ D w : ℝ, ∀ z : ℕ,
      1 < D → 2 ≤ w → w ≤ z → 3 ≤ sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
          lowerContinuousPartial N (sieveParameter D p - 1) * buchstabCoefficient P z p) ≤
        upperContinuousPartial N (sieveParameter D z) +
          2 * K * lowerContinuousPartial N (sieveParameter D z - 1) / Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_allContinuousTerms_bound
  refine ⟨K, hK, ?_⟩
  intro N D w z hD hw hwz hs P hP hodd
  calc
    _ = ∑ k ∈ range N, ∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
        rosserContinuousTerm (2 * k + 2) (sieveParameter D p - 1) * buchstabCoefficient P z p := by
      simp only [lowerContinuousPartial, sum_mul]
      rw [sum_comm]
    _ ≤ ∑ k ∈ range N, (rosserContinuousTerm (2 * k + 3) (sieveParameter D z) +
        2 * K * rosserContinuousTerm (2 * k + 2) (sieveParameter D z - 1) / Real.log w) := by
      apply sum_le_sum
      intro k _
      convert! hb (2 * k + 1) D w z hD hw hwz (by
        simpa [rosserContinuousCutoff, Nat.even_add, Nat.even_mul] using hs) P hP hodd using 1
    _ = _ := by
      rw [upperContinuousPartial_eq_tail N _ hs]
      simp only [sum_add_distrib, lowerContinuousPartial, ← sum_div, ← mul_sum]

theorem weighted_buchstab_upperContinuousPartial_auxiliary :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∀ D w : ℝ, ∀ z : ℕ,
      1 < D → 2 ≤ w → w ≤ z → 2 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
          upperContinuousPartial N (sieveParameter D p - 1) * buchstabCoefficient P z p) ≤
        lowerContinuousPartial (N + 1) (sieveParameter D z) +
          2 * K * ((sieveParameter D z - 1) * upperAuxiliaryError (sieveParameter D z - 1)) /
            Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_upperContinuousPartial
  refine ⟨K, hK, ?_⟩
  intro N D w z hD hw hwz hs P hP hodd
  apply (hb N D w z hD hw hwz hs.le P hP hodd).trans
  apply _root_.add_le_add le_rfl
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (upperContinuousPartial_le_mul_auxiliary N _ (by linarith)) (by positivity))
      (Real.log_pos (by linarith)).le

theorem weighted_buchstab_lowerContinuousPartial_auxiliary :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∀ D w : ℝ, ∀ z : ℕ,
      1 < D → 2 ≤ w → w ≤ z → 3 ≤ sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
          lowerContinuousPartial N (sieveParameter D p - 1) * buchstabCoefficient P z p) ≤
        upperContinuousPartial N (sieveParameter D z) +
          2 * K * ((sieveParameter D z - 1) * lowerAuxiliaryError (sieveParameter D z - 1)) /
            Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_lowerContinuousPartial
  refine ⟨K, hK, ?_⟩
  intro N D w z hD hw hwz hs P hP hodd
  apply (hb N D w z hD hw hwz hs P hP hodd).trans
  apply _root_.add_le_add le_rfl
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (lowerContinuousPartial_le_mul_auxiliary N _ (by linarith)) (by positivity))
      (Real.log_pos (by linarith)).le

end Chen.LinearSieve
