import Submission.ChenTheorem.Lemma9.LinearSieve.SieveProductAsymptotics
import Submission.ChenTheorem.Lemma5.EulerPenalty
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit true

open Filter
open scoped Classical

namespace Chen.LinearSieve

noncomputable def powerSieveCutoff (a : ℝ) (x : ℕ) : ℕ := ⌊(x : ℝ) ^ a⌋₊

theorem powerSieveCutoff_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (powerSieveCutoff a) atTop atTop :=
  tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)

theorem powerSieveCutoff_div_rpow_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℕ => (powerSieveCutoff a x : ℝ) / (x : ℝ) ^ a) atTop (nhds 1) := by
  simpa only [Function.comp_def, powerSieveCutoff] using
    tendsto_nat_floor_div_atTop.comp ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)

theorem primeFactors_card_div_powerSieveCutoff_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℕ => (x.primeFactors.card : ℝ) / powerSieveCutoff a x) atTop (nhds 0) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow := (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hbase := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun x : ℕ => (2 / Real.log 2) * (Real.log x / (x : ℝ) ^ a)) atTop
      (nhds 0) := by simpa only [Function.comp_def, mul_zero] using hbase.const_mul (2 / Real.log 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun x => by positivity)
  · filter_upwards [eventually_ge_atTop (2 : ℕ), hpow.eventually (eventually_ge_atTop (2 : ℝ))]
      with x hx hp
    change 2 ≤ (x : ℝ) ^ a at hp
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hp0 := Real.rpow_pos_of_pos hxpos a
    have hf := Nat.lt_floor_add_one ((x : ℝ) ^ a)
    have hhalf : (x : ℝ) ^ a / 2 ≤ (powerSieveCutoff a x : ℝ) := by
      unfold powerSieveCutoff
      linarith
    have hfpos : (0 : ℝ) < powerSieveCutoff a x := (half_pos hp0).trans_le hhalf
    have hlog : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
    have hc : (x.primeFactors.card : ℝ) ≤ Real.log x / Real.log 2 :=
      (le_div_iff₀ hlog2).mpr (primeFactors_card_mul_log_two_le_log (by omega))
    calc
      _ ≤ (Real.log x / Real.log 2) / powerSieveCutoff a x :=
        div_le_div_of_nonneg_right hc hfpos.le
      _ ≤ (Real.log x / Real.log 2) / ((x : ℝ) ^ a / 2) :=
        div_le_div_of_nonneg_left (div_nonneg hlog hlog2.le) (half_pos hp0) hhalf
      _ = _ := by ring

theorem log_powerSieveCutoff_div_log_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℕ => Real.log (powerSieveCutoff a x) / Real.log x) atTop (nhds a) := by
  have hratio := powerSieveCutoff_div_rpow_tendsto a ha
  have hlogratio : Tendsto (fun x : ℕ =>
      Real.log ((powerSieveCutoff a x : ℝ) / (x : ℝ) ^ a)) atTop (nhds 0) := by
    simpa only [Real.log_one] using hratio.log one_ne_zero
  have hsmall := hlogratio.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim := (tendsto_const_nhds (x := a)).add hsmall
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    (powerSieveCutoff_tendsto a ha).eventually (eventually_ge_atTop 2)] with x hx hy
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hypos : (0 : ℝ) < powerSieveCutoff a x := by exact_mod_cast (show 0 < powerSieveCutoff a x by omega)
  have hlog : Real.log (x : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
  dsimp only [Function.comp_apply]
  rw [Real.log_div (ne_of_gt hypos) (ne_of_gt (Real.rpow_pos_of_pos hxpos a)), Real.log_rpow hxpos]
  field_simp
  ring

/-- The uniform singular-series normalization for every fixed positive
power cutoff. For Chen's cutoff `a=1/10`, the limit is `20 exp(-γ)`. -/
theorem primeSieveProduct_power_normalized_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℕ => (primeSieveProduct x (powerSieveCutoff a x) / chenConst x) * Real.log x)
      atTop (nhds (2 * Real.exp (-Real.eulerMascheroniConstant) / a)) := by
  have hprod := primeSieveProduct_log_normalized_tendsto (powerSieveCutoff a)
    (powerSieveCutoff_tendsto a ha) (primeFactors_card_div_powerSieveCutoff_tendsto a ha)
  have hlim := hprod.div (log_powerSieveCutoff_div_log_tendsto a ha) (ne_of_gt ha)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    (powerSieveCutoff_tendsto a ha).eventually (eventually_ge_atTop 2)] with x hx hy
  have hlogx : Real.log (x : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < x by omega)))
  have hlogy : Real.log (powerSieveCutoff a x : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < powerSieveCutoff a x by omega)))
  have hC : chenConst x ≠ 0 := ne_of_gt (twinConst_pos.trans_le (twinConst_le_chenConst x))
  dsimp only [Pi.div_apply]
  field_simp

end Chen.LinearSieve
