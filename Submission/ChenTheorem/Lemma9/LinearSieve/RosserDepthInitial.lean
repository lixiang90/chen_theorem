import Submission.ChenTheorem.Lemma9.LinearSieve.RosserDepthTransport

set_option autoImplicit true
open Filter
open scoped Topology

namespace Chen.LinearSieve

/-- For an upper continuous depth, its parameter-weighted value is
constant on the initial interval. -/
theorem mul_rosserContinuousTerm_initial (n : ℕ)
    (hc : rosserContinuousCutoff (n + 2) = 3) (s : ℝ) (hs : 0 < s) (hs3 : s ≤ 3) :
    s * rosserContinuousTerm (n + 2) s = 3 * rosserContinuousTerm (n + 2) 3 := by
  simpa only [hc] using mul_rosserContinuousTerm_constant_below n s hs (hc ▸ hs3)

/-- Any fixed upper depth transfers from the strict cube-root cutoff to
the whole initial interval. The local estimate above three remains explicit. -/
theorem eventually_rosser_depth_small_parameter_bound (n : ℕ)
    (hc : rosserContinuousCutoff (n + 2) = 3) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ z : ℕ, 2 ≤ z → 1 < sieveParameter D z → sieveParameter D z ≤ 3 →
      rosserRelativeStoppingMass P (n + 2) (rosserCubeCutoff D + 1) true D ≤
        rosserContinuousTerm (n + 2) (sieveParameter D (rosserCubeCutoff D)) + ε / 16 →
      rosserRelativeStoppingMass P (n + 2) (z + 1) true D ≤
        rosserContinuousTerm (n + 2) (sieveParameter D z) + ε := by
  obtain ⟨K, hK, hb⟩ := rosser_depth_transport_numerator_bound
  let A := 3 * rosserContinuousTerm (n + 2) 3
  have hA : 0 ≤ A := mul_nonneg (by norm_num)
    (rosserContinuousTerm_nonneg (n + 2) 3 (by norm_num))
  have hB : 0 < A + ε / 2 := by positivity
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp rosserCubeCutoff_tendsto)
  have hlim : Tendsto (fun D : ℝ => K * (A + ε / 2) / Real.log (rosserCubeCutoff D))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    rosserCubeCutoff_tendsto.eventually (eventually_ge_atTop 2),
    sieveParameter_rosserCubeCutoff_tendsto.eventually (gt_mem_nhds (by norm_num : (3 : ℝ) < 4)),
    hlim.eventually (gt_mem_nhds (show 0 < ε / 2 by positivity))]
      with D hD hm hσ herr
  intro P hP hodd z hz hs hs3 hmajor
  have hmz := rosserCubeCutoff_le_of_parameter_le_three D hD hm z hz hs3
  have hcube := (rosserCubeCutoff_cube_bounds D (by linarith)).2
  have hsmooth := sieveParameter_rosserCubeCutoff_gt_three D hD hm
  have hweighted := antitoneOn_mul_rosserContinuousTerm (n + 2)
    (by norm_num : (0 : ℝ) < 3)
    (show 0 < sieveParameter D (rosserCubeCutoff D) by linarith) hsmooth.le
  have hnum : sieveParameter D (rosserCubeCutoff D) *
      rosserRelativeStoppingMass P (n + 2) (rosserCubeCutoff D + 1) true D ≤ A + ε / 2 := by
    have h := mul_le_mul_of_nonneg_left hmajor
      (show 0 ≤ sieveParameter D (rosserCubeCutoff D) by linarith)
    dsimp only at hweighted
    dsimp only [A]
    nlinarith
  have h := hb n D (rosserCubeCutoff D) z hD hm hmz hcube P hP hodd (A + ε / 2) hnum
  have hs0 : 0 < sieveParameter D z := by linarith
  have hlm : 0 < Real.log (rosserCubeCutoff D) :=
    Real.log_pos (by exact_mod_cast (show 1 < rosserCubeCutoff D by omega))
  have hinitial := mul_rosserContinuousTerm_initial n hc (sieveParameter D z) hs0 hs3
  have hmain : (A + ε / 2) / sieveParameter D z ≤
      rosserContinuousTerm (n + 2) (sieveParameter D z) + ε / 2 := by
    rw [div_le_iff₀ hs0]
    dsimp only [A]
    nlinarith
  have hdensity : K * (A + ε / 2) /
      (Real.log (rosserCubeCutoff D) * sieveParameter D z) ≤ ε / 2 := by
    rw [← div_div, div_le_iff₀ hs0]
    nlinarith
  linarith

/-- The large-parameter comparison suffices for the entire upper domain
at any fixed noninitial upper depth. This isolates the induction step from
the special handling of parameters between one and three. -/
theorem rosser_depth_upper_comparison_of_large_parameter (n : ℕ)
    (hc : rosserContinuousCutoff (n + 2) = 3)
    (hlarge : ∀ ε : ℝ, 0 < ε → ∀ᶠ D : ℝ in atTop,
      ∀ z : ℕ, 2 ≤ z → 3 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      rosserRelativeStoppingMass P (n + 2) (z + 1) true D ≤
        rosserContinuousTerm (n + 2) (sieveParameter D z) + ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ D : ℝ in atTop,
      ∀ z : ℕ, 2 ≤ z → 1 < sieveParameter D z →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      rosserRelativeStoppingMass P (n + 2) (z + 1) true D ≤
        rosserContinuousTerm (n + 2) (sieveParameter D z) + ε := by
  intro ε hε
  filter_upwards [hlarge ε hε, hlarge (ε / 16) (by positivity),
    eventually_rosser_depth_small_parameter_bound n hc ε hε,
    eventually_gt_atTop (1 : ℝ),
    rosserCubeCutoff_tendsto.eventually (eventually_ge_atTop 2)]
      with D hb hlocal hsmall hD hm
  intro z hz hs P hP hodd
  by_cases hs3 : 3 < sieveParameter D z
  · exact hb z hz hs3 P hP hodd
  · apply hsmall P hP hodd z hz hs (le_of_not_gt hs3)
    exact hlocal (rosserCubeCutoff D) hm (sieveParameter_rosserCubeCutoff_gt_three D hD hm)
      P hP hodd

end Chen.LinearSieve
