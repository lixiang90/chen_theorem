import Submission.ChenTheorem.Lemma9.LinearSieve.BuchstabAuxiliary

set_option autoImplicit true
open Finset Set MeasureTheory

namespace Chen.LinearSieve

theorem sum_auxiliaryErrorScale_child (δ D w : ℝ) (z : ℕ) (H : ℝ → ℝ) (P : Finset ℕ)
    (hD : 1 < D) (hw : 2 ≤ w) (hz : 2 ≤ z) (hs : 1 < sieveParameter D z) :
    (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
      auxiliaryErrorScale δ (D / p) (sieveParameter (D / p) p) H * buchstabCoefficient P z p) =
    (Real.log D) ^ (-δ) * (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
      childAuxiliaryWeight δ (sieveParameter D p) * H (sieveParameter D p - 1) *
        buchstabCoefficient P z p) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpI := Finset.mem_Ioc.mp hp
  have hp2 : 2 ≤ p := (Nat.le_floor hw).trans hpI.1.le
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
  have hz1 : 1 < (z : ℝ) := by exact_mod_cast (show 1 < z by omega)
  have hsp := (sieveParameter_antitone hD) hp1 hz1 (Nat.cast_le.mpr hpI.2)
  rw [auxiliaryErrorScale_child δ D p H hD hp1 (hs.trans_le hsp)]
  ring

theorem weighted_buchstab_auxiliary_level_lower :
    ∃ K : ℝ, 0 < K ∧ ∀ δ D w : ℝ, ∀ z : ℕ,
      0 ≤ δ → δ ≤ 1 → 1 < D → 2 ≤ w → w ≤ z → 3 ≤ sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
          auxiliaryErrorScale δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError *
            buchstabCoefficient P z p) ≤
        auxiliaryErrorScale δ D (sieveParameter D z) upperAuxiliaryError +
        2 * K * auxiliaryErrorScale δ (D / z) (sieveParameter (D / z) z) lowerAuxiliaryError /
          Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_auxiliary_lower_bound
  refine ⟨K, hK, ?_⟩
  intro δ D w z hδ hδ1 hD hw hwz hs P hP hodd
  have hz : 2 ≤ z := by exact_mod_cast hw.trans hwz
  have hz1 : 1 < (z : ℝ) := by exact_mod_cast (show 1 < z by omega)
  have hs1 : 1 < sieveParameter D z := by linarith
  have h := mul_le_mul_of_nonneg_left (hb δ D w z hδ hδ1 hD hw hwz hs P hP hodd)
    (Real.rpow_nonneg (Real.log_pos hD).le (-δ))
  rw [sum_auxiliaryErrorScale_child δ D w z lowerAuxiliaryError P hD hw hz hs1,
    auxiliaryErrorScale_child δ D z lowerAuxiliaryError hD hz1 hs1]
  convert! h using 1
  dsimp [auxiliaryErrorScale]
  ring

theorem weighted_buchstab_auxiliary_level_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ δ D w : ℝ, ∀ z : ℕ,
      0 ≤ δ → δ ≤ 1 → 1 < D → 2 ≤ w → w ≤ z → 2 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
        (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
          auxiliaryErrorScale δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError *
            buchstabCoefficient P z p) ≤
        auxiliaryErrorScale δ D (sieveParameter D z) lowerAuxiliaryError +
        2 * K * auxiliaryErrorScale δ (D / z) (sieveParameter (D / z) z) upperAuxiliaryError /
          Real.log w := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_auxiliary_upper_bound
  refine ⟨K, hK, ?_⟩
  intro δ D w z hδ hδ1 hD hw hwz hs P hP hodd
  have hz : 2 ≤ z := by exact_mod_cast hw.trans hwz
  have hz1 : 1 < (z : ℝ) := by exact_mod_cast (show 1 < z by omega)
  have hs1 : 1 < sieveParameter D z := by linarith
  have h := mul_le_mul_of_nonneg_left (hb δ D w z hδ hδ1 hD hw hwz hs P hP hodd)
    (Real.rpow_nonneg (Real.log_pos hD).le (-δ))
  rw [sum_auxiliaryErrorScale_child δ D w z upperAuxiliaryError P hD hw hz hs1,
    auxiliaryErrorScale_child δ D z upperAuxiliaryError hD hz1 hs1]
  convert! h using 1
  dsimp [auxiliaryErrorScale]
  ring

end Chen.LinearSieve
