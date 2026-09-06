import ChenTheorem.Lemma9.LinearSieve.BuchstabInflated
import ChenTheorem.Lemma9.LinearSieve.RosserPartialDefect

open Set MeasureTheory Filter

namespace Chen.LinearSieve

theorem sum_inflatedAuxiliaryError_child_le (d δ D w : ℝ) (z : ℕ) (H : ℝ → ℝ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, 2 < p)
    (hd : 1 ≤ d) (hD : 1 < D) (hw : 2 ≤ w) (hz : 2 ≤ z) (hs : 1 < sieveParameter D z)
    (hH : ∀ s : ℝ, sieveParameter D z ≤ s → 0 ≤ H (s - 1)) :
    (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
      inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) H * buchstabCoefficient P z p) ≤
    (Real.log D) ^ (-δ) * (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
      inflatedChildAuxiliaryWeight d δ D (sieveParameter D p) H * buchstabCoefficient P z p) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpI := Finset.mem_Ioc.mp hp
  have hp2 : 2 ≤ p := (Nat.le_floor hw).trans hpI.1.le
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
  have hz1 : 1 < (z : ℝ) := by exact_mod_cast (show 1 < z by omega)
  have hsp := (sieveParameter_antitone hD) hp1 hz1 (Nat.cast_le.mpr hpI.2)
  have h := inflatedAuxiliaryError_child_le d δ D p H hd hD hp1 (hs.trans_le hsp) (hH _ hsp)
  have hn := normalized_buchstab_mass_nonneg P hP hodd (z + 1) p
  change 0 ≤ buchstabCoefficient P z p at hn
  have hm := mul_le_mul_of_nonneg_right h hn
  dsimp only [inflatedChildAuxiliaryWeight]
  nlinarith

/-- The true child-level errors are bounded by the inflated integral and
its explicit dimension-one terminal loss, uniformly in the prime set. -/
theorem weighted_buchstab_inflated_level_lower :
    ∃ K : ℝ, 0 < K ∧ ∀ d δ : ℝ, 1 ≤ d → -1 ≤ δ → ∀ᶠ D in atTop,
      ∀ w : ℝ, ∀ z : ℕ, 2 ≤ w → w ≤ z → 3 ≤ sieveParameter D z →
      sieveParameter D w ≤ 2 * growingSieveParameter d (Real.log D) + 1 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
        inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) lowerAuxiliaryError * buchstabCoefficient P z p) ≤
      (Real.log D) ^ (-δ) * ((1 / sieveParameter D z) *
        (∫ s in Ioc (sieveParameter D z) (sieveParameter D w), inflatedChildAuxiliaryWeight d δ D s lowerAuxiliaryError) +
        2 * K * inflatedChildAuxiliaryWeight d δ D (sieveParameter D z) lowerAuxiliaryError / Real.log w) := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_inflated_lower
  refine ⟨K, hK, ?_⟩
  intro d δ hd hδ
  filter_upwards [hb d δ (by linarith) hδ, eventually_gt_atTop (1 : ℝ)] with D hbound hD
  intro w z hw hwz hs hcut P hP hodd
  have hz : 2 ≤ z := by exact_mod_cast hw.trans hwz
  have h := sum_inflatedAuxiliaryError_child_le d δ D w z lowerAuxiliaryError P hP hodd hd hD hw hz
    (by linarith) (fun s hsp => lowerAuxiliaryError_nonneg _ (by linarith))
  exact h.trans (mul_le_mul_of_nonneg_left (hbound w z hw hwz hs hcut P hP hodd)
    (Real.rpow_nonneg (Real.log_pos hD).le (-δ)))

theorem weighted_buchstab_inflated_level_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ d δ : ℝ, 1 ≤ d → -1 < δ → ∀ᶠ D in atTop,
      ∀ w : ℝ, ∀ z : ℕ, 2 ≤ w → w ≤ z → 2 < sieveParameter D z →
      sieveParameter D w ≤ 2 * growingSieveParameter d (Real.log D) + 1 →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      (∑ p ∈ Finset.Ioc ⌊w⌋₊ z,
        inflatedAuxiliaryError d δ (D / p) (sieveParameter (D / p) p) upperAuxiliaryError * buchstabCoefficient P z p) ≤
      (Real.log D) ^ (-δ) * ((1 / sieveParameter D z) *
        (∫ s in Ioc (sieveParameter D z) (sieveParameter D w), inflatedChildAuxiliaryWeight d δ D s upperAuxiliaryError) +
        2 * K * inflatedChildAuxiliaryWeight d δ D (sieveParameter D z) upperAuxiliaryError / Real.log w) := by
  obtain ⟨K, hK, hb⟩ := weighted_buchstab_inflated_upper
  refine ⟨K, hK, ?_⟩
  intro d δ hd hδ
  filter_upwards [hb d δ (by linarith) hδ, eventually_gt_atTop (1 : ℝ)] with D hbound hD
  intro w z hw hwz hs hcut P hP hodd
  have hz : 2 ≤ z := by exact_mod_cast hw.trans hwz
  have h := sum_inflatedAuxiliaryError_child_le d δ D w z upperAuxiliaryError P hP hodd hd hD hw hz
    (by linarith) (fun s hsp => upperAuxiliaryError_nonneg _ (by linarith))
  exact h.trans (mul_le_mul_of_nonneg_left (hbound w z hw hwz hs hcut P hP hodd)
    (Real.rpow_nonneg (Real.log_pos hD).le (-δ)))

end Chen.LinearSieve
