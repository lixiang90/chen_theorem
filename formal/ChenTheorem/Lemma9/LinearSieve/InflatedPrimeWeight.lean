import ChenTheorem.Lemma9.LinearSieve.InflatedChildInitialWeight

open Filter Set

namespace Chen.LinearSieve

/-- Positivity turns weighted decrease into ordinary decrease; composing
with the sieve parameter reverses it to the prime-size direction. -/
theorem sieveParameter_weight_monotone_of_weighted_antitone (D w z : ℝ)
    (hD : 1 < D) (hw : 2 ≤ w) (H : ℝ → ℝ)
    (hn : ∀ s ∈ Icc (sieveParameter D z) (sieveParameter D w), 0 ≤ H s)
    (ha : AntitoneOn (fun s => s * H s) (Icc (sieveParameter D z) (sieveParameter D w))) :
    MonotoneOn (fun t => H (sieveParameter D t)) (Icc w z) := by
  intro x hx y hy hxy
  have hxs := sieveParameter_mem_Icc hD hw hx
  have hys := sieveParameter_mem_Icc hD hw hy
  have hst := sieveParameter_antitone hD (by change 1 < x; linarith [hx.1])
    (by change 1 < y; linarith [hy.1]) hxy
  have h := ha hys hxs hst
  have hm := mul_le_mul_of_nonneg_right hst (hn _ hxs)
  have hspos := sieveParameter_pos hD (show 1 < y by linarith [hy.1])
  dsimp only at h ⊢
  nlinarith

/-- At sufficiently large levels the lower-child majorant meets both shape
conditions of weighted Buchstab summation, uniformly over the prime interval. -/
theorem eventually_inflatedPrimeLowerWeight_shape (d δ : ℝ) (hd : 0 < d) (hδ : -1 ≤ δ) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      3 ≤ sieveParameter D z → sieveParameter D w ≤ 2 * growingSieveParameter d (Real.log D) + 1 →
      MonotoneOn (fun t => inflatedChildAuxiliaryWeight d δ D (sieveParameter D t) lowerAuxiliaryError) (Icc w z) ∧
      ∀ t ∈ Icc w z,
        inflatedChildAuxiliaryWeight d δ D (sieveParameter D t) lowerAuxiliaryError * Real.log z ≤
          inflatedChildAuxiliaryWeight d δ D (sieveParameter D z) lowerAuxiliaryError * Real.log t := by
  filter_upwards [eventually_inflatedChildLowerWeight_antitone d δ hd hδ] with D hD
  refine ⟨hD.1, ?_⟩
  intro w z hw hwz hs hcut
  have ha := hD.2.mono (show Icc (sieveParameter D z) (sieveParameter D w) ⊆
      Icc 3 (2 * growingSieveParameter d (Real.log D) + 1) from
    fun _ ht => ⟨hs.trans ht.1, ht.2.trans hcut⟩)
  refine ⟨sieveParameter_weight_monotone_of_weighted_antitone D w z hD.1 hw
    (fun s => inflatedChildAuxiliaryWeight d δ D s lowerAuxiliaryError) ?_ ha,
    sieveParameter_weight_log_growth D w z hD.1 hw hwz _ ha⟩
  intro s ht
  exact inflatedChildAuxiliaryWeight_nonneg d δ D s lowerAuxiliaryError hD.1
    (by linarith [ht.1]) (lowerAuxiliaryError_nonneg _ (by linarith [ht.1]))

theorem eventually_inflatedPrimeUpperWeight_shape (d δ : ℝ) (hd : 0 < d) (hδ : -1 < δ) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧ ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      2 < sieveParameter D z → sieveParameter D w ≤ 2 * growingSieveParameter d (Real.log D) + 1 →
      MonotoneOn (fun t => inflatedChildAuxiliaryWeight d δ D (sieveParameter D t) upperAuxiliaryError) (Icc w z) ∧
      ∀ t ∈ Icc w z,
        inflatedChildAuxiliaryWeight d δ D (sieveParameter D t) upperAuxiliaryError * Real.log z ≤
          inflatedChildAuxiliaryWeight d δ D (sieveParameter D z) upperAuxiliaryError * Real.log t := by
  filter_upwards [eventually_inflatedChildUpperWeight_antitone d δ hd hδ] with D hD
  refine ⟨hD.1, ?_⟩
  intro w z hw hwz hs hcut
  have ha := hD.2.mono (show Icc (sieveParameter D z) (sieveParameter D w) ⊆
      Ioc 2 (2 * growingSieveParameter d (Real.log D) + 1) from
    fun _ ht => ⟨hs.trans_le ht.1, ht.2.trans hcut⟩)
  refine ⟨sieveParameter_weight_monotone_of_weighted_antitone D w z hD.1 hw
    (fun s => inflatedChildAuxiliaryWeight d δ D s upperAuxiliaryError) ?_ ha,
    sieveParameter_weight_log_growth D w z hD.1 hw hwz _ ha⟩
  intro s ht
  exact inflatedChildAuxiliaryWeight_nonneg d δ D s upperAuxiliaryError hD.1
    (by linarith [ht.1]) (upperAuxiliaryError_nonneg _ (by linarith [ht.1]))

end Chen.LinearSieve
