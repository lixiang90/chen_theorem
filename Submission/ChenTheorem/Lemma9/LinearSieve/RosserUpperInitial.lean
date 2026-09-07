import Submission.ChenTheorem.Lemma9.LinearSieve.RosserCubeCutoff

set_option autoImplicit true
open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem rosserCubeCutoff_le_of_parameter_le_three (D : ℝ) (hD : 1 < D)
    (hm : 2 ≤ rosserCubeCutoff D) (z : ℕ) (hz : 2 ≤ z)
    (hs : sieveParameter D z ≤ 3) : rosserCubeCutoff D ≤ z := by
  by_contra h
  have hzm : z ≤ rosserCubeCutoff D := by omega
  have hzR : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hmR : (1 : ℝ) < rosserCubeCutoff D := by exact_mod_cast (show 1 < rosserCubeCutoff D by omega)
  have ha := sieveParameter_antitone hD hzR hmR (by exact_mod_cast hzm)
  have hsm := sieveParameter_rosserCubeCutoff_gt_three D hD hm
  linarith

/-- Uniform reduction of the whole initial upper interval to a single
cutoff with parameter strictly greater than three. The remaining local
error hypothesis belongs to the smooth-parameter iteration. -/
theorem eventually_rosser_upper_small_parameter_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, 2 < p) →
      ∀ z : ℕ, 2 ≤ z → 1 < sieveParameter D z → sieveParameter D z ≤ 3 →
      rosserRelativeDefect P (rosserCubeCutoff D + 1) true D ≤
        upperContinuousError (sieveParameter D (rosserCubeCutoff D)) + ε / 16 →
      rosserRelativeDefect P (z + 1) true D ≤ upperContinuousError (sieveParameter D z) + ε := by
  have hlocal := rosserCubeCutoff_tendsto.eventually (eventually_rosser_upper_initial_comparison ε hε)
  have hσ := sieveParameter_rosserCubeCutoff_tendsto.eventually
    (gt_mem_nhds (by norm_num : (3 : ℝ) < 4))
  have hF := weighted_upperFunction_rosserCubeCutoff_tendsto.eventually
    (gt_mem_nhds (show linearSieveInitialConstant < linearSieveInitialConstant + ε / 4 by linarith))
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    rosserCubeCutoff_tendsto.eventually (eventually_ge_atTop 2), hlocal, hσ, hF]
    with D hD hm hlocal hσ hF
  intro P hP hodd z hz hs hs3 hmajor
  have hmz := rosserCubeCutoff_le_of_parameter_le_three D hD hm z hz hs3
  have hcube := (rosserCubeCutoff_cube_bounds D (by linarith)).2
  have hsmooth := sieveParameter_rosserCubeCutoff_gt_three D hD hm
  have hnum0 := mul_le_mul_of_nonneg_left (_root_.add_le_add (show (1 : ℝ) ≤ 1 from le_rfl) hmajor)
    (show 0 ≤ sieveParameter D (rosserCubeCutoff D) by linarith)
  have hnum : sieveParameter D (rosserCubeCutoff D) *
      (1 + rosserRelativeDefect P (rosserCubeCutoff D + 1) true D) ≤
        linearSieveInitialConstant + ε / 2 := by
    dsimp only [upperLinearSieveFunction] at hF
    nlinarith
  exact hlocal D z hD hmz hcube hs hs3 P hP hodd hnum

end Chen.LinearSieve
