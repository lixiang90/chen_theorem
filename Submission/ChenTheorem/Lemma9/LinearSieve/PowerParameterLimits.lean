import Submission.ChenTheorem.Lemma9.LinearSieve.RoundedLevelBounds
import Submission.ChenTheorem.Lemma9.LinearSieve.SieveParameter

set_option autoImplicit true
open Filter
open scoped Topology

namespace Chen.LinearSieve

theorem powerSieveCutoff_succ_div_rpow_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℕ => ((powerSieveCutoff a x : ℝ) + 1) / (x : ℝ) ^ a) atTop (𝓝 1) := by
  have h := (powerSieveCutoff_div_rpow_tendsto a ha).add
    (((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop)
  simpa only [add_div, one_div, add_zero, Pi.inv_apply, Function.comp_def] using h

theorem log_powerSieveCutoff_succ_div_log_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℕ => Real.log ((powerSieveCutoff a x : ℝ) + 1) / Real.log x) atTop (𝓝 a) := by
  have hr : Tendsto (fun x : ℕ => Real.log (((powerSieveCutoff a x : ℝ) + 1) / (x : ℝ) ^ a))
      atTop (𝓝 0) := by
    simpa only [Real.log_one] using (powerSieveCutoff_succ_div_rpow_tendsto a ha).log one_ne_zero
  have h := (tendsto_const_nhds (x := a)).add
    (hr.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
  dsimp only [Function.comp_def]
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlog : Real.log (x : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < x by omega))).ne'
  rw [Real.log_div (by positivity) (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0]
  field_simp
  ring

theorem log_div_smallCutoff_succ_tendsto :
    Tendsto (fun x : ℕ => Real.log x /
      Real.log ((powerSieveCutoff (1 / 10) x : ℝ) + 1)) atTop (𝓝 10) := by
  have h := (log_powerSieveCutoff_succ_div_log_tendsto (1 / 10) (by norm_num)).inv₀
    (by norm_num : (1 / 10 : ℝ) ≠ 0)
  simpa only [inv_div, inv_div_left, one_mul, div_one] using h

theorem sieveParameter_powerSieveCutoff_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℕ => sieveParameter (powerSieveCutoff a x)
      ((powerSieveCutoff (1 / 10) x : ℝ) + 1)) atTop (𝓝 (10 * a)) := by
  have h := (log_powerSieveCutoff_div_log_tendsto a ha).mul log_div_smallCutoff_succ_tendsto
  rw [mul_comm a 10] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
  have hlog : Real.log (x : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < x by omega))).ne'
  unfold sieveParameter
  field_simp

end Chen.LinearSieve
