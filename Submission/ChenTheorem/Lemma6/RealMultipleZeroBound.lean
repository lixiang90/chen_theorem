import Submission.ChenTheorem.Lemma6.RealZeroUniquenessTools
import Submission.ChenTheorem.Analysis.MultipleZeroPoleRealPart

set_option autoImplicit true
open Set Metric

namespace Chen

theorem primitive_LFunction_logDeriv_re_ge_multiple_real_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive)
    (σ β : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) (hβ : 15 / 16 < β)
    (hf : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hdf : deriv (DirichletCharacter.LFunction χ) (β : ℂ) = 0) :
    2 / (σ - β) - 60000 * Real.log ((q : ℝ) * 2) ≤
      (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re := by
  have hβ' : β ≤ 1 := by
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; have := congrArg Complex.re he; simp at this; linarith))
      (by simpa using hh.le)) hf
  let c := dirichletZeroDiskCenter 0
  let w := (β : ℂ) - c
  let z := (σ : ℂ) - c
  have hw : w ∈ ball 0 (3 / 8) := by
    rw [mem_ball_zero_iff]
    simpa [w, c] using norm_near_real_zero_shift_lt hβ hβ' (t := 0) (by norm_num)
  have he : c + w = (β : ℂ) := by dsimp [w]; ring
  have hf' : DirichletCharacter.LFunction χ (c + w) = 0 := by rw [he]; exact hf
  have hdf' : deriv (fun u => DirichletCharacter.LFunction χ (c + u)) w = 0 := by
    rw [deriv_comp_const_add, he]
    exact hdf
  have h0 : DirichletCharacter.LFunction χ (c + 0) ≠ 0 :=
    centered_LFunction_ne_zero_of_re_gt_neg_quarter χ 0 0 (by norm_num)
  have hp := two_div_re_gap_le_diskZeroPoleSum_re_of_zero_deriv (κ := -(1 / 4 : ℝ))
    (by norm_num : (0 : ℝ) < 3 / 8) (primitive_centered_LFunction_analytic hq hχ 0) h0
    (fun u _ hu => centered_LFunction_ne_zero_of_re_gt_neg_quarter χ 0 u hu)
    (z := z) (by dsimp [z, c]; simp [dirichletZeroDiskCenter]; linarith)
    hw hf' hdf' (by simp [w, z, c, dirichletZeroDiskCenter])
  have hre : z.re - w.re = σ - β := by simp [z, w]
  rw [hre] at hp
  have hsne : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; have := congrArg Complex.re he; simp at this; linarith))
      (by simpa using hσ.le)
  have hb := norm_LFunction_logDeriv_sub_local_zero_poles_le_log hq hχ 0 (σ : ℂ)
    (by simpa using norm_line_point_sub_dirichletZeroDiskCenter_le hσ hσ' 0) hsne
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  simp only [Complex.sub_re, abs_zero, zero_add] at hr
  change -(60000 * Real.log ((q : ℝ) * 2)) ≤
    (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re -
      (diskZeroPoleSum (fun u => DirichletCharacter.LFunction χ (c + u)) (3 / 8) z).re at hr
  linarith

end Chen
