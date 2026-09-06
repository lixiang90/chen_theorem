import ChenTheorem.Lemma9.LinearSieve.RosserUpperComparison

open Filter
open scoped Topology

namespace Chen.LinearSieve

/-- The strict integer cutoff below the positive cube root. The ceiling
convention handles exact cubes without landing on the joining point. -/
noncomputable def rosserCubeCutoff (D : ℝ) : ℕ := ⌈D ^ ((3 : ℝ)⁻¹)⌉₊ - 1

theorem rosserCubeCutoff_cast (D : ℝ) (hD : 0 < D) :
    (rosserCubeCutoff D : ℝ) = (⌈D ^ ((3 : ℝ)⁻¹)⌉₊ : ℝ) - 1 := by
  have hr := Real.rpow_pos_of_pos hD ((3 : ℝ)⁻¹)
  have hc : 1 ≤ ⌈D ^ ((3 : ℝ)⁻¹)⌉₊ := by
    have h : 0 < ⌈D ^ ((3 : ℝ)⁻¹)⌉₊ := by rwa [Nat.lt_ceil, Nat.cast_zero]
    omega
  simp only [rosserCubeCutoff, Nat.cast_sub hc, Nat.cast_one]

theorem rosserCubeCutoff_root_bounds (D : ℝ) (hD : 0 < D) :
    D ^ ((3 : ℝ)⁻¹) - 1 ≤ (rosserCubeCutoff D : ℝ) ∧
      (rosserCubeCutoff D : ℝ) < D ^ ((3 : ℝ)⁻¹) := by
  rw [rosserCubeCutoff_cast D hD]
  have hle := Nat.le_ceil (D ^ ((3 : ℝ)⁻¹))
  have hlt := Nat.ceil_lt_add_one (Real.rpow_nonneg hD.le ((3 : ℝ)⁻¹))
  constructor <;> linarith

theorem rosserCubeCutoff_cube_bounds (D : ℝ) (hD : 0 < D) :
    (rosserCubeCutoff D : ℝ) ^ 3 < D ∧ D ≤ ((rosserCubeCutoff D + 1 : ℕ) : ℝ) ^ 3 := by
  have hr := rosserCubeCutoff_root_bounds D hD
  have heq : (D ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ) = D :=
    Real.rpow_inv_natCast_pow hD.le (by norm_num)
  constructor
  · calc
      _ < (D ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ) := by gcongr; exact hr.2
      _ = D := heq
  · have hc : D ^ ((3 : ℝ)⁻¹) ≤ ((rosserCubeCutoff D + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [hr.1]
    calc
      D = (D ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ) := heq.symm
      _ ≤ _ := by gcongr

theorem rosserCubeCutoff_tendsto : Tendsto rosserCubeCutoff atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hroot := tendsto_rpow_atTop (by norm_num : 0 < (3 : ℝ)⁻¹)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hroot.eventually (eventually_ge_atTop ((b : ℝ) + 1))] with D hD hroot
  have h := (rosserCubeCutoff_root_bounds D hD).1
  have hb : (b : ℝ) ≤ rosserCubeCutoff D := by linarith
  exact_mod_cast hb

theorem rosserCubeCutoff_div_root_tendsto :
    Tendsto (fun D : ℝ => (rosserCubeCutoff D : ℝ) / D ^ ((3 : ℝ)⁻¹)) atTop (𝓝 1) := by
  have hroot := tendsto_rpow_atTop (by norm_num : 0 < (3 : ℝ)⁻¹)
  have hc := tendsto_nat_ceil_div_atTop.comp hroot
  have hi := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hroot
  have h := hc.sub hi
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  rw [rosserCubeCutoff_cast D hD, sub_div]
  rfl

theorem log_rosserCubeCutoff_div_log_tendsto :
    Tendsto (fun D : ℝ => Real.log (rosserCubeCutoff D) / Real.log D) atTop (𝓝 ((3 : ℝ)⁻¹)) := by
  have hr : Tendsto (fun D : ℝ => Real.log ((rosserCubeCutoff D : ℝ) / D ^ ((3 : ℝ)⁻¹)))
      atTop (𝓝 0) := by
    simpa only [Real.log_one] using rosserCubeCutoff_div_root_tendsto.log one_ne_zero
  have hsmall := hr.div_atTop Real.tendsto_log_atTop
  have hlim := (tendsto_const_nhds (x := (3 : ℝ)⁻¹)).add hsmall
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    rosserCubeCutoff_tendsto.eventually (eventually_ge_atTop 2)] with D hD hm
  have hm0 : (0 : ℝ) < rosserCubeCutoff D := by exact_mod_cast (show 0 < rosserCubeCutoff D by omega)
  have hD0 : 0 < D := by linarith
  have hl0 := (Real.log_pos hD).ne'
  rw [Real.log_div hm0.ne' (Real.rpow_pos_of_pos hD0 _).ne', Real.log_rpow hD0]
  field_simp
  ring

theorem sieveParameter_rosserCubeCutoff_tendsto :
    Tendsto (fun D : ℝ => sieveParameter D (rosserCubeCutoff D)) atTop (𝓝 3) := by
  have h := log_rosserCubeCutoff_div_log_tendsto.inv₀ (by norm_num)
  simpa only [inv_div, inv_inv, sieveParameter] using h

theorem sieveParameter_rosserCubeCutoff_gt_three (D : ℝ) (hD : 1 < D)
    (hm : 2 ≤ rosserCubeCutoff D) : 3 < sieveParameter D (rosserCubeCutoff D) := by
  have hm1 : (1 : ℝ) < rosserCubeCutoff D := by exact_mod_cast (show 1 < rosserCubeCutoff D by omega)
  have hm0 : (0 : ℝ) < rosserCubeCutoff D := by linarith
  have hcube := (rosserCubeCutoff_cube_bounds D (by linarith)).1
  have hl := Real.log_lt_log (pow_pos hm0 3) hcube
  rw [Real.log_pow] at hl
  unfold sieveParameter
  apply (lt_div_iff₀ (Real.log_pos hm1)).mpr
  norm_num at hl ⊢
  exact hl

/-- The continuous weighted numerator at this strict cutoff approaches
the initial normalization from the side used by the smooth upper step. -/
theorem weighted_upperFunction_rosserCubeCutoff_tendsto :
    Tendsto (fun D : ℝ => sieveParameter D (rosserCubeCutoff D) *
      upperLinearSieveFunction (sieveParameter D (rosserCubeCutoff D))) atTop (𝓝 linearSieveInitialConstant) := by
  have hc : ContinuousAt upperLinearSieveFunction (3 : ℝ) :=
    (continuousOn_upperLinearSieveFunction 3 (by norm_num)).continuousAt
      (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 3))
  have h := sieveParameter_rosserCubeCutoff_tendsto.mul
    (hc.tendsto.comp sieveParameter_rosserCubeCutoff_tendsto)
  have heq : 3 * upperLinearSieveFunction 3 = linearSieveInitialConstant := by
    rw [upperLinearSieveFunction_initial 3 (by norm_num) le_rfl]
    ring
  rwa [heq] at h

end Chen.LinearSieve
