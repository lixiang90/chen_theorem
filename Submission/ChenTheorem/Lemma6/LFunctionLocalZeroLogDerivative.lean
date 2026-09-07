import Submission.ChenTheorem.Lemma6.LFunctionEulerBounds
import Submission.ChenTheorem.Analysis.LocalZeroLogDerivativeBound
import Mathlib.Analysis.Calculus.Deriv.Shift

set_option autoImplicit true

open Set Metric

namespace Chen

noncomputable def dirichletZeroDiskCenter (t : ℝ) : ℂ :=
  ((5 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I

noncomputable def dirichletZeroDiskBound (q : ℕ) (t : ℝ) : ℝ :=
  6 * Real.sqrt q * Real.log (2 * q) * (‖dirichletZeroDiskCenter t‖ + 1 / 2) + 1

theorem dirichletZeroDiskCenter_re (t : ℝ) : (dirichletZeroDiskCenter t).re = 5 / 4 := by
  simp [dirichletZeroDiskCenter]

theorem dirichletZeroDiskBound_ge_one (q : ℕ) (hq : 2 ≤ q) (t : ℝ) :
    1 ≤ dirichletZeroDiskBound q t := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hl : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have : 0 ≤ 6 * Real.sqrt q * Real.log (2 * q) * (‖dirichletZeroDiskCenter t‖ + 1 / 2) := by positivity
  unfold dirichletZeroDiskBound
  linarith

theorem norm_LFunction_centered_disk_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive)
    (t : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w)‖ ≤ dirichletZeroDiskBound q t := by
  let c := dirichletZeroDiskCenter t
  let B : ℝ := 3 * Real.sqrt q * Real.log (2 * q)
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hl : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hr : 1 / 2 ≤ (c + w).re := by
    have h := Complex.abs_re_le_norm w
    rw [Complex.add_re, dirichletZeroDiskCenter_re]
    have := (abs_le.mp h).1
    linarith
  have hn : ‖c + w‖ ≤ ‖c‖ + 1 / 2 := (norm_add_le c w).trans (by linarith)
  have h := norm_LFunction_le_of_re_pos hχ hq (show 0 < (c + w).re by linarith)
  change ‖DirichletCharacter.LFunction χ (c + w)‖ ≤ B * ‖c + w‖ / (c + w).re at h
  apply h.trans
  apply (div_le_iff₀ (by linarith : 0 < (c + w).re)).mpr
  have he : dirichletZeroDiskBound q t = 2 * B * (‖c‖ + 1 / 2) + 1 := by
    dsimp [dirichletZeroDiskBound, B, c]
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hn hB,
    mul_le_mul_of_nonneg_left hr (mul_nonneg hB (show 0 ≤ ‖c‖ + 1 / 2 by positivity))]

theorem norm_LFunction_zero_disk_center_ge {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (1 / 5 : ℝ) ≤ ‖DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t)‖ := by
  have h := norm_LFunction_euler_lower χ (dirichletZeroDiskCenter t)
    (by rw [dirichletZeroDiskCenter_re]; norm_num)
  norm_num only [dirichletZeroDiskCenter_re] at h
  exact h

/-- A primitive Dirichlet L-function admits a local zero-pole expansion
with an explicit growth error. The zeros may lie anywhere in the disk;
only the evaluation point is required to be nonzero. -/
theorem norm_LFunction_logDeriv_sub_local_zero_poles_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (t : ℝ)
    (s : ℂ) (hs : ‖s - dirichletZeroDiskCenter t‖ ≤ 9 / 32)
    (hne : DirichletCharacter.LFunction χ s ≠ 0) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
      diskZeroPoleSum (fun w => DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w))
        (3 / 8) (s - dirichletZeroDiskCenter t)‖ ≤
      640 * (Real.log (5 * dirichletZeroDiskBound q t) + 1) := by
  let c := dirichletZeroDiskCenter t
  let F := fun w => DirichletCharacter.LFunction χ (c + w)
  let M := dirichletZeroDiskBound q t
  have hM : 1 ≤ M := dirichletZeroDiskBound_ge_one q hq t
  have hχne : χ ≠ 1 := by
    intro he
    have hcond := DirichletCharacter.eq_one_iff_conductor_eq_one.mp he
    rw [DirichletCharacter.isPrimitive_def] at hχ
    omega
  have hdiff : Differentiable ℂ F :=
    (DirichletCharacter.differentiable_LFunction hχne).comp (by fun_prop)
  have hf : AnalyticOnNhd ℂ F (closedBall 0 (4 * (3 / 8) / 3)) :=
    (hdiff.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)
  have hanchor : (1 / 5 : ℝ) ≤ ‖F 0‖ := by
    simpa only [F, add_zero] using norm_LFunction_zero_disk_center_ge χ t
  have hnorm0 : 0 < ‖F 0‖ := by linarith
  have hb : ∀ w ∈ sphere (0 : ℂ) (4 * (3 / 8) / 3), ‖F w‖ ≤ M := by
    intro w hw
    have hw' : ‖w‖ ≤ 1 / 2 := by norm_num [mem_sphere] at hw; exact hw.le
    exact norm_LFunction_centered_disk_le hq hχ t hw'
  have he : c + (s - c) = s := by ring
  have hmain := norm_logDeriv_sub_zero_poles_le_of_outer_bound (by norm_num : (0 : ℝ) < 3 / 8)
    hM hf (norm_pos_iff.mp hnorm0) hb
    (show ‖s - c‖ ≤ 3 * (3 / 8) / 4 by norm_num; exact hs)
    (show F (s - c) ≠ 0 by simpa only [F, he] using hne)
  have hd : deriv F (s - c) = deriv (DirichletCharacter.LFunction χ) s := by
    dsimp [F]
    rw [deriv_comp_const_add, he]
  rw [hd, show F (s - c) = DirichletCharacter.LFunction χ s by dsimp [F]; rw [he]] at hmain
  have hratio : M / ‖F 0‖ ≤ 5 * M := (div_le_iff₀ hnorm0).mpr (by nlinarith)
  have hlogs := Real.log_le_log (div_pos (by linarith : 0 < M) hnorm0) hratio
  apply hmain.trans
  change 240 * (Real.log (M / ‖F 0‖) + 1) / (3 / 8) ≤ 640 * (Real.log (5 * M) + 1)
  linarith

end Chen
