import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Chen

theorem exists_small_power_disk_radius {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ 3 * r ≤ 1 / 4 ∧ r < 1 / 4 ∧
      3 * Real.log 3 ≤ ε * (Real.log (1 / 4 : ℝ) - Real.log r) := by
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  let M : ℝ := 3 * Real.log 3 / ε + Real.log 3 + 1
  have hM : Real.log (3 : ℝ) < M := by
    have h := div_nonneg (show 0 ≤ 3 * Real.log (3 : ℝ) by positivity) hε.le
    dsimp [M]
    linarith
  have hM0 : 0 < M := hlog.trans hM
  let r : ℝ := Real.exp (Real.log (1 / 4 : ℝ) - M)
  have hr : 0 < r := Real.exp_pos _
  have hlogr : Real.log r = Real.log (1 / 4 : ℝ) - M := Real.log_exp _
  have hrsmall : r ≤ 1 / 12 := by
    calc
      r ≤ Real.exp (Real.log (1 / 4 : ℝ) - Real.log 3) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_sub, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]; norm_num
  refine ⟨r, hr, by linarith, by linarith, ?_⟩
  rw [hlogr]
  have hratio : 3 * Real.log (3 : ℝ) / ε ≤ M := by dsimp [M]; linarith
  have h := (div_le_iff₀ hε).mp hratio
  nlinarith

end Chen
