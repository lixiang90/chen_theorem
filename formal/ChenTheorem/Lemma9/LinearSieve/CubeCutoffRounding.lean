import ChenTheorem.Lemma9.LinearSieve.RosserCubeCutoff
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem log_add_one_sub_log_le (x : ℝ) (hx : 0 < x) :
    Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < x + 1) hx)
  rw [Real.log_div (by linarith : x + 1 ≠ 0) hx.ne'] at h
  convert! h using 1
  field_simp
  ring

theorem sieveParameter_rosserCubeCutoff_gap (D : ℝ) (hD : 1 < D)
    (hm : 2 ≤ rosserCubeCutoff D) :
    0 ≤ sieveParameter D (rosserCubeCutoff D) - 3 ∧
      sieveParameter D (rosserCubeCutoff D) - 3 ≤
        3 / ((rosserCubeCutoff D : ℝ) * Real.log (rosserCubeCutoff D)) := by
  have hm1 : (1 : ℝ) < rosserCubeCutoff D := by exact_mod_cast (show 1 < rosserCubeCutoff D by omega)
  have hm0 : (0 : ℝ) < rosserCubeCutoff D := by linarith
  have hlog := Real.log_pos hm1
  have hc := (rosserCubeCutoff_cube_bounds D (by linarith)).2
  have hl := Real.log_le_log (by linarith : 0 < D) hc
  simp only [Real.log_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hl
  have hr := log_add_one_sub_log_le (rosserCubeCutoff D) hm0
  refine ⟨by linarith [sieveParameter_rosserCubeCutoff_gt_three D hD hm], ?_⟩
  apply (le_div_iff₀ (mul_pos hm0 hlog)).mpr
  have ht : sieveParameter D (rosserCubeCutoff D) * Real.log (rosserCubeCutoff D) = Real.log D := by
    unfold sieveParameter
    field_simp
  have hr' := (le_div_iff₀ hm0).mp hr
  nlinarith

theorem weighted_upperFunction_le_initial_add (t : ℝ) (ht : 3 ≤ t) :
    t * upperLinearSieveFunction t ≤ linearSieveInitialConstant + (t - 3) := by
  have h := antitoneOn_mul_upperContinuousError (by norm_num : (1 : ℝ) < 3)
    (show 1 < t by linarith) ht
  unfold upperLinearSieveFunction linearSieveInitialConstant
  linarith

/-- Integer rounding at the strict cube cutoff is smaller than every fixed
inverse power of the logarithm, including the powers in the sieve error. -/
theorem tendsto_log_rpow_mul_cubeCutoff_gap (a : ℝ) :
    Tendsto (fun D : ℝ => (Real.log D) ^ a * (sieveParameter D (rosserCubeCutoff D) - 3))
      atTop (𝓝 0) := by
  have hlim := ((isLittleO_log_rpow_rpow_atTop a (by norm_num : (0 : ℝ) < (3 : ℝ)⁻¹)).tendsto_div_nhds_zero).mul_const (6 / Real.log 2)
  simp only [zero_mul] at hlim
  have hev : ∀ᶠ D : ℝ in atTop, 0 ≤ (Real.log D) ^ a * (sieveParameter D (rosserCubeCutoff D) - 3) ∧
      (Real.log D) ^ a * (sieveParameter D (rosserCubeCutoff D) - 3) ≤
        ((Real.log D) ^ a / D ^ ((3 : ℝ)⁻¹)) * (6 / Real.log 2) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      rosserCubeCutoff_tendsto.eventually_ge_atTop 2,
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (3 : ℝ)⁻¹)).eventually_ge_atTop 2] with D hD hm hr
    have hm1 : (1 : ℝ) < rosserCubeCutoff D := by exact_mod_cast (show 1 < rosserCubeCutoff D by omega)
    have hm0 : (0 : ℝ) < rosserCubeCutoff D := by linarith
    have hroot := Real.rpow_pos_of_pos (by linarith : 0 < D) ((3 : ℝ)⁻¹)
    have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hlogm := Real.log_pos hm1
    have hlogle := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ rosserCubeCutoff D by exact_mod_cast hm)
    have hmroot : D ^ ((3 : ℝ)⁻¹) / 2 ≤ rosserCubeCutoff D := by
      have h := (rosserCubeCutoff_root_bounds D (by linarith)).1
      linarith
    have hden : D ^ ((3 : ℝ)⁻¹) * Real.log 2 / 2 ≤
        (rosserCubeCutoff D : ℝ) * Real.log (rosserCubeCutoff D) := by
      have h := mul_le_mul hmroot hlogle hlog2.le hm0.le
      nlinarith
    have hfrac := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3)
      (by positivity : 0 < D ^ ((3 : ℝ)⁻¹) * Real.log 2 / 2) hden
    have hgap := sieveParameter_rosserCubeCutoff_gap D hD hm
    have hp := Real.rpow_nonneg (Real.log_pos hD).le a
    refine ⟨mul_nonneg hp hgap.1, ?_⟩
    have h := mul_le_mul_of_nonneg_left (hgap.2.trans hfrac) hp
    convert! h using 1
    field_simp
    ring
  exact squeeze_zero' (hev.mono fun _ h => h.1) (hev.mono fun _ h => h.2) hlim

end Chen.LinearSieve
