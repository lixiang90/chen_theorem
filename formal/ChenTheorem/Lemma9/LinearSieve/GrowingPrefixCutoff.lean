import ChenTheorem.Lemma9.LinearSieve.RosserGrowingParameter
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem tendsto_growingSieveParameter_div_self (d : ℝ) (hd : 1 < d) :
    Tendsto (fun L => growingSieveParameter d L / L) atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  have hr : 0 < 1 - 1 / d := by
    have := (div_lt_one hd0).2 hd
    linarith
  have h := (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  have hL0 : 0 < L := by linarith
  unfold growingSieveParameter
  rw [Real.rpow_sub hL0, Real.rpow_one]
  field_simp

theorem tendsto_level_div_growingSieveParameter (d : ℝ) (hd : 1 < d) :
    Tendsto (fun L => L / (2 * growingSieveParameter d L)) atTop atTop := by
  have hwithin : Tendsto (fun L => growingSieveParameter d L / L) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_growingSieveParameter_div_self d hd, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
    exact div_pos (growingSieveParameter_pos d L hL) (by linarith)
  have h := (tendsto_inv_nhdsGT_zero.comp hwithin).atTop_div_const (by norm_num : (0 : ℝ) < 2)
  simpa only [Function.comp_def, inv_div, div_div, mul_comm] using h

noncomputable def growingPrefixCutoff (d D : ℝ) : ℝ :=
  Real.exp (Real.log D / (2 * growingSieveParameter d (Real.log D)))

noncomputable def growingPrefixIndex (d D : ℝ) : ℕ := ⌊growingPrefixCutoff d D⌋₊

theorem growingPrefixCutoff_pos (d D : ℝ) : 0 < growingPrefixCutoff d D := Real.exp_pos _

theorem log_growingPrefixCutoff (d D : ℝ) :
    Real.log (growingPrefixCutoff d D) = Real.log D / (2 * growingSieveParameter d (Real.log D)) :=
  Real.log_exp _

theorem tendsto_growingPrefixCutoff_atTop (d : ℝ) (hd : 1 < d) :
    Tendsto (growingPrefixCutoff d) atTop atTop :=
  Real.tendsto_exp_atTop.comp ((tendsto_level_div_growingSieveParameter d hd).comp Real.tendsto_log_atTop)

theorem sieveParameter_growingPrefixCutoff (d D : ℝ) (hL : 1 < Real.log D) :
    sieveParameter D (growingPrefixCutoff d D) = 2 * growingSieveParameter d (Real.log D) := by
  have hL0 : Real.log D ≠ 0 := by linarith
  have hσ := (growingSieveParameter_pos d (Real.log D) hL).ne'
  rw [sieveParameter, log_growingPrefixCutoff]
  field_simp

theorem growingPrefixIndex_parameter_bounds (d D : ℝ) (hD : 1 < D) (hL : 1 < Real.log D)
    (hw : 2 ≤ growingPrefixCutoff d D) :
    2 ≤ growingPrefixIndex d D ∧
      growingSieveParameter d (Real.log D) ≤ sieveParameter D (growingPrefixIndex d D + 1) ∧
      sieveParameter D (growingPrefixIndex d D + 1) ≤ 2 * growingSieveParameter d (Real.log D) := by
  have hm : 2 ≤ growingPrefixIndex d D := Nat.le_floor hw
  have hmR : (2 : ℝ) ≤ growingPrefixIndex d D := by exact_mod_cast hm
  have hfloor := Nat.floor_le (growingPrefixCutoff_pos d D).le
  have hfloorlt := Nat.lt_floor_add_one (growingPrefixCutoff d D)
  change growingPrefixCutoff d D < (growingPrefixIndex d D : ℝ) + 1 at hfloorlt
  change (growingPrefixIndex d D : ℝ) ≤ growingPrefixCutoff d D at hfloor
  have hm1 : (1 : ℝ) < (growingPrefixIndex d D : ℝ) + 1 := by linarith
  have hpow : (growingPrefixIndex d D : ℝ) + 1 ≤ growingPrefixCutoff d D ^ 2 := by nlinarith
  have hlogs := Real.log_le_log (by linarith : 0 < (growingPrefixIndex d D : ℝ) + 1) hpow
  rw [Real.log_pow] at hlogs
  norm_num only [Nat.cast_ofNat] at hlogs
  have hσ := growingSieveParameter_pos d (Real.log D) hL
  have he : growingSieveParameter d (Real.log D) * (2 * Real.log (growingPrefixCutoff d D)) =
      Real.log D := by rw [log_growingPrefixCutoff]; field_simp
  have hmul := mul_le_mul_of_nonneg_left hlogs hσ.le
  rw [he] at hmul
  refine ⟨hm, ?_, ?_⟩
  · exact (le_div_iff₀ (Real.log_pos hm1)).mpr hmul
  · have h := sieveParameter_antitone hD (show growingPrefixCutoff d D ∈ Set.Ioi 1 by
      change 1 < growingPrefixCutoff d D; linarith) hm1 hfloorlt.le
    rwa [sieveParameter_growingPrefixCutoff d D hL] at h

theorem eventually_growingPrefixCutoff_properties (d : ℝ) (hd : 1 < d) :
    ∀ᶠ D in atTop, 1 < D ∧ 1 < Real.log D ∧ 2 ≤ growingPrefixCutoff d D ∧
      2 ≤ growingPrefixIndex d D ∧
      growingSieveParameter d (Real.log D) ≤ sieveParameter D (growingPrefixIndex d D + 1) ∧
      sieveParameter D (growingPrefixIndex d D + 1) ≤ 2 * growingSieveParameter d (Real.log D) ∧
      (((growingPrefixIndex d D + 1 : ℕ) : ℝ)) ^ 2 < D := by
  have hg := (tendsto_growingSieveParameter_atTop d (by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_gt_atTop 1,
    (tendsto_growingPrefixCutoff_atTop d hd).eventually_ge_atTop 2,
      hg.eventually_ge_atTop 6] with D hD hL hw hσ
  dsimp only [Function.comp_def] at hσ
  obtain ⟨hm, hlo, hhi⟩ := growingPrefixIndex_parameter_bounds d D hD hL hw
  refine ⟨hD, hL, hw, hm, hlo, hhi, ?_⟩
  have hmR : (2 : ℝ) ≤ growingPrefixIndex d D := by exact_mod_cast hm
  have hs : 2 < sieveParameter D (growingPrefixIndex d D + 1) := by linarith
  have hlog := (lt_div_iff₀ (Real.log_pos (by linarith : (1 : ℝ) < (growingPrefixIndex d D : ℝ) + 1))).mp hs
  apply (Real.log_lt_log_iff (pow_pos (by positivity) 2) (by linarith : 0 < D)).mp
  rw [Real.log_pow]
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hlog

end Chen.LinearSieve
