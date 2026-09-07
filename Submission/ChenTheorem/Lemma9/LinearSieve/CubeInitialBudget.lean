import Submission.ChenTheorem.Lemma9.LinearSieve.CubeCutoffRounding
import Submission.ChenTheorem.Lemma9.LinearSieve.GrowingPrefixCutoff

set_option autoImplicit true
open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem tendsto_growing_log_rpow_div (d δ : ℝ) (hgap : δ + 1 / d < 1) :
    Tendsto (fun L : ℝ => growingSieveParameter d L * L ^ δ / L) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by linarith : 0 < 1 - δ - 1 / d)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  have hL0 : 0 < L := by linarith
  unfold growingSieveParameter
  rw [Real.rpow_sub hL0, Real.rpow_sub hL0, Real.rpow_one]
  field_simp

theorem tendsto_growing_log_rpow_cube_gap (d δ : ℝ) :
    Tendsto (fun D : ℝ => growingSieveParameter d (Real.log D) * (Real.log D) ^ δ *
      (sieveParameter D (rosserCubeCutoff D) - 3)) atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have h := (tendsto_log_rpow_mul_cubeCutoff_gap (δ + 1 / d + 1)).mul hlog
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with D hD
  have hL := Real.log_pos hD
  dsimp only [Function.comp_def, id_eq]
  unfold growingSieveParameter
  rw [Real.rpow_add hL, Real.rpow_add hL, Real.rpow_one]
  field_simp

/-- Both the sieve-product density loss and the cube-rounding excess fit
inside the inverse-growing-parameter budget relative to the full error. -/
theorem tendsto_cube_initial_density_budget (d δ K : ℝ) (hgap : δ + 1 / d < 1) :
    Tendsto (fun D : ℝ => growingSieveParameter d (Real.log D) * (Real.log D) ^ δ *
      (K / Real.log (rosserCubeCutoff D) +
        (1 + K / Real.log (rosserCubeCutoff D)) *
          (sieveParameter D (rosserCubeCutoff D) - 3) / linearSieveInitialConstant)) atTop (𝓝 0) := by
  have hb := (tendsto_growing_log_rpow_div d δ hgap).comp Real.tendsto_log_atTop
  have hm := (hb.const_mul K).mul sieveParameter_rosserCubeCutoff_tendsto
  have hk := (sieveParameter_rosserCubeCutoff_tendsto.const_mul K).div_atTop Real.tendsto_log_atTop
  have hf := ((tendsto_const_nhds (x := (1 : ℝ))).add hk).div_const linearSieveInitialConstant
  have h := hm.add ((tendsto_growing_log_rpow_cube_gap d δ).mul hf)
  simp only [mul_zero, zero_mul, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    rosserCubeCutoff_tendsto.eventually_ge_atTop 2] with D hD hm
  have hL := (Real.log_pos hD).ne'
  have hlogm := (Real.log_pos (show (1 : ℝ) < rosserCubeCutoff D by
    exact_mod_cast (show 1 < rosserCubeCutoff D by omega))).ne'
  dsimp only [Function.comp_def]
  unfold sieveParameter
  field_simp

theorem eventually_cube_initial_density_budget (d δ K ε : ℝ) (hd : 1 < d)
    (hgap : δ + 1 / d < 1) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, 1 < D ∧
      (Real.log D) ^ δ * (K / Real.log (rosserCubeCutoff D) +
        (1 + K / Real.log (rosserCubeCutoff D)) *
          (sieveParameter D (rosserCubeCutoff D) - 3) / linearSieveInitialConstant) ≤
        ε / growingSieveParameter d (Real.log D) := by
  filter_upwards [eventually_growingPrefixCutoff_properties d hd,
    (tendsto_cube_initial_density_budget d δ K hgap).eventually (gt_mem_nhds hε)] with D hc hb
  rcases hc with ⟨hD, hL, hw, hm, hlo, hhi, hlevel⟩
  refine ⟨hD, (le_div_iff₀ (growingSieveParameter_pos d (Real.log D) hL)).mpr ?_⟩
  convert! hb.le using 1
  ring

end Chen.LinearSieve
