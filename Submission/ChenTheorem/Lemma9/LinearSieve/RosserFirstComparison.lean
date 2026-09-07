import Submission.ChenTheorem.Lemma9.LinearSieve.RosserFirstMass

set_option autoImplicit true
open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem firstContinuousTerm_ge_linear (s : ℝ) (hs : 0 < s) :
    (3 - s) / s ≤ rosserContinuousTerm 1 s := by
  rw [rosserContinuousTerm_one s hs]
  exact div_le_div_of_nonneg_right (le_max_left _ _) hs.le

/-- The first actual stopping term is bounded by the first continuous
term with explicit rounding and density losses. -/
theorem rosserFirstMass_le_continuous_with_error :
    ∃ K : ℝ, 0 < K ∧ ∀ D : ℝ, 1 < D → 2 ≤ rosserCubeCutoff D →
      ∀ z : ℕ, 2 ≤ z → 1 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      rosserRelativeStoppingMass P 1 (z + 1) true D ≤ rosserContinuousTerm 1 (sieveParameter D z) +
        (sieveParameter D (rosserCubeCutoff D) - 3) / sieveParameter D z +
        K * sieveParameter D (rosserCubeCutoff D) / (Real.log (rosserCubeCutoff D) * sieveParameter D z) := by
  obtain ⟨K, hK, hb⟩ := primeDensity_sieveProduct_dimension_one
  refine ⟨K, hK, ?_⟩
  intro D hD hm z hz hs P hP hodd
  have hmR : (1 : ℝ) < rosserCubeCutoff D := by exact_mod_cast (show 1 < rosserCubeCutoff D by omega)
  have hzR : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hσ := sieveParameter_rosserCubeCutoff_gt_three D hD hm
  have hs0 : 0 < sieveParameter D z := by linarith
  have hlm := Real.log_pos hmR
  by_cases hzm : z ≤ rosserCubeCutoff D
  · unfold rosserRelativeStoppingMass
    rw [rosserStoppingMass_one_eq_zero_below_cube P hP z D (by linarith) hzm, zero_div]
    have hf := rosserContinuousTerm_nonneg 1 (sieveParameter D z) hs0
    positivity
  · have hmz : rosserCubeCutoff D ≤ z := by omega
    rw [rosserRelativeStoppingMass_one_eq_ratio P hP hodd z D (by linarith) hmz]
    have h := hb (rosserCubeCutoff D) z hm hmz P hP hodd
    rw [← sieveParameter_ratio D (rosserCubeCutoff D) z hD hmR hzR] at h
    have hf := firstContinuousTerm_ge_linear (sieveParameter D z) hs0
    calc
      _ ≤ (1 + K / Real.log (rosserCubeCutoff D)) *
          (sieveParameter D (rosserCubeCutoff D) / sieveParameter D z) - 1 := sub_le_sub_right h 1
      _ = (3 - sieveParameter D z) / sieveParameter D z +
          (sieveParameter D (rosserCubeCutoff D) - 3) / sieveParameter D z +
          K * sieveParameter D (rosserCubeCutoff D) / (Real.log (rosserCubeCutoff D) * sieveParameter D z) := by
        field_simp
        ring
      _ ≤ _ := by linarith

theorem firstStoppingComparisonError_tendsto (K : ℝ) :
    Tendsto (fun D : ℝ => (sieveParameter D (rosserCubeCutoff D) - 3) +
      K * sieveParameter D (rosserCubeCutoff D) / Real.log (rosserCubeCutoff D)) atTop (𝓝 0) := by
  have hσ := sieveParameter_rosserCubeCutoff_tendsto
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp rosserCubeCutoff_tendsto)
  have h := (hσ.sub_const 3).add ((hσ.const_mul K).div_atTop hlog)
  simpa only [sub_self, add_zero, Function.comp_def] using h

/-- The base case of the depth comparison is uniform in the prime set
and all terminal parameters `s>1`; no recursive comparison is assumed. -/
theorem eventually_rosserFirstMass_le_continuous (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ z : ℕ, 2 ≤ z → 1 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      rosserRelativeStoppingMass P 1 (z + 1) true D ≤ rosserContinuousTerm 1 (sieveParameter D z) + ε := by
  obtain ⟨K, hK, hb⟩ := rosserFirstMass_le_continuous_with_error
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    rosserCubeCutoff_tendsto.eventually (eventually_ge_atTop 2),
    (firstStoppingComparisonError_tendsto K).eventually (gt_mem_nhds hε)] with D hD hm herr
  intro z hz hs P hP hodd
  have h := hb D hD hm z hz hs P hP hodd
  have hs0 : 0 < sieveParameter D z := by linarith
  have he : (sieveParameter D (rosserCubeCutoff D) - 3) / sieveParameter D z +
      K * sieveParameter D (rosserCubeCutoff D) / (Real.log (rosserCubeCutoff D) * sieveParameter D z) ≤ ε := by
    have hrewrite : (sieveParameter D (rosserCubeCutoff D) - 3) / sieveParameter D z +
        K * sieveParameter D (rosserCubeCutoff D) / (Real.log (rosserCubeCutoff D) * sieveParameter D z) =
        ((sieveParameter D (rosserCubeCutoff D) - 3) +
          K * sieveParameter D (rosserCubeCutoff D) / Real.log (rosserCubeCutoff D)) / sieveParameter D z := by ring
    rw [hrewrite, div_le_iff₀ hs0]
    nlinarith
  linarith

end Chen.LinearSieve
