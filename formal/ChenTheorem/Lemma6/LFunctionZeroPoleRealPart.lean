import ChenTheorem.Lemma6.LFunctionLocalZeroScale
import ChenTheorem.Analysis.ZeroPoleRealPart
import Mathlib.NumberTheory.LSeries.Nonvanishing

open Set Metric

namespace Chen

theorem line_point_sub_dirichletZeroDiskCenter (σ t : ℝ) :
    (σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t = ((σ - 5 / 4 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [dirichletZeroDiskCenter]

theorem norm_line_point_sub_dirichletZeroDiskCenter_le {σ : ℝ}
    (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) (t : ℝ) :
    ‖(σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t‖ ≤ 9 / 32 := by
  rw [line_point_sub_dirichletZeroDiskCenter, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith

theorem primitive_centered_LFunction_analytic {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (t : ℝ) :
    AnalyticOnNhd ℂ (fun w => DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w))
      (closedBall 0 (3 / 8)) := by
  have hχne : χ ≠ 1 := by
    intro he
    have hcond := DirichletCharacter.eq_one_iff_conductor_eq_one.mp he
    rw [DirichletCharacter.isPrimitive_def] at hχ
    omega
  have hd := (DirichletCharacter.differentiable_LFunction hχne).comp
    (show Differentiable ℂ (fun w => dirichletZeroDiskCenter t + w) by fun_prop)
  exact (hd.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ _)

theorem centered_LFunction_ne_zero_of_re_gt_neg_quarter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) (w : ℂ) (hw : -(1 / 4 : ℝ) < w.re) :
    DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w) ≠ 0 := by
  have hr : 1 < (dirichletZeroDiskCenter t + w).re := by
    rw [Complex.add_re, dirichletZeroDiskCenter_re]
    linarith
  apply DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr _) hr.le
  intro he
  rw [he] at hr
  norm_num at hr

theorem primitive_LFunction_local_zero_poles_re_nonneg {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ (diskZeroPoleSum
      (fun w => DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w)) (3 / 8)
      ((σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t)).re := by
  apply diskZeroPoleSum_re_nonneg (κ := -(1 / 4 : ℝ)) (primitive_centered_LFunction_analytic hq hχ t)
    (fun w _ hw => centered_LFunction_ne_zero_of_re_gt_neg_quarter χ t w hw)
  rw [line_point_sub_dirichletZeroDiskCenter, Complex.ofReal_re]
  linarith

theorem primitive_LFunction_logDeriv_re_ge {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (σ t : ℝ)
    (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) :
    -(60000 * Real.log ((q : ℝ) * (|t| + 2))) ≤
      (deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  have he : dirichletZeroDiskCenter t +
      ((σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t) =
      (σ : ℂ) + (t : ℂ) * Complex.I := by ring
  have hne := centered_LFunction_ne_zero_of_re_gt_neg_quarter χ t
    ((σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t)
    (by rw [line_point_sub_dirichletZeroDiskCenter, Complex.ofReal_re]; linarith)
  rw [he] at hne
  have hb := norm_LFunction_logDeriv_sub_local_zero_poles_le_log hq hχ t _
    (norm_line_point_sub_dirichletZeroDiskCenter_le hσ hσ' t) hne
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  rw [Complex.sub_re] at hr
  have hp := primitive_LFunction_local_zero_poles_re_nonneg hq hχ σ t hσ
  linarith

theorem primitive_LFunction_local_zero_poles_re_ge_single {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (σ β t : ℝ)
    (hσ : 1 < σ) (hβ : 7 / 8 < β)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (t : ℂ) * Complex.I) = 0) :
    1 / (σ - β) ≤ (diskZeroPoleSum
      (fun w => DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + w)) (3 / 8)
      ((σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t)).re := by
  let c := dirichletZeroDiskCenter t
  let w := (β : ℂ) + (t : ℂ) * Complex.I - c
  let z := (σ : ℂ) + (t : ℂ) * Complex.I - c
  have hwr : w.re = β - 5 / 4 := by simp [w, c, line_point_sub_dirichletZeroDiskCenter]
  have hzr : z.re = σ - 5 / 4 := by simp [z, c, line_point_sub_dirichletZeroDiskCenter]
  have he : c + w = (β : ℂ) + (t : ℂ) * Complex.I := by dsimp [w]; ring
  have hβ' : β ≤ 1 := by
    by_contra! hh
    have h := centered_LFunction_ne_zero_of_re_gt_neg_quarter χ t w (by rw [hwr]; linarith)
    rw [he] at h
    exact h hzero
  have hw : w ∈ ball 0 (3 / 8 : ℝ) := by
    rw [mem_ball_zero_iff]
    dsimp [w, c]
    rw [line_point_sub_dirichletZeroDiskCenter, Complex.norm_real, Real.norm_eq_abs]
    apply abs_lt.mpr
    constructor <;> linarith
  have h0 : DirichletCharacter.LFunction χ (dirichletZeroDiskCenter t + 0) ≠ 0 := by
    have h := norm_LFunction_zero_disk_center_ge χ t
    rw [add_zero]
    exact norm_pos_iff.mp (by linarith)
  have hp := one_div_re_gap_le_diskZeroPoleSum_re (κ := -(1 / 4 : ℝ))
    (by norm_num : (0 : ℝ) < 3 / 8) (primitive_centered_LFunction_analytic hq hχ t) h0
    (fun u _ hu => centered_LFunction_ne_zero_of_re_gt_neg_quarter χ t u hu)
    (z := z) (by rw [hzr]; linarith) hw
    (by change DirichletCharacter.LFunction χ (c + w) = 0; rw [he]; exact hzero)
    (by simp [w, z, c, line_point_sub_dirichletZeroDiskCenter])
  rw [hzr, hwr, show σ - 5 / 4 - (β - 5 / 4) = σ - β by ring] at hp
  exact hp

theorem primitive_LFunction_logDeriv_re_ge_single_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (σ β t : ℝ)
    (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) (hβ : 7 / 8 < β)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (t : ℂ) * Complex.I) = 0) :
    1 / (σ - β) - 60000 * Real.log ((q : ℝ) * (|t| + 2)) ≤
      (deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by
  have he : dirichletZeroDiskCenter t +
      ((σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t) =
      (σ : ℂ) + (t : ℂ) * Complex.I := by ring
  have hne := centered_LFunction_ne_zero_of_re_gt_neg_quarter χ t
    ((σ : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter t)
    (by rw [line_point_sub_dirichletZeroDiskCenter, Complex.ofReal_re]; linarith)
  rw [he] at hne
  have hb := norm_LFunction_logDeriv_sub_local_zero_poles_le_log hq hχ t _
    (norm_line_point_sub_dirichletZeroDiskCenter_le hσ hσ' t) hne
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  rw [Complex.sub_re] at hr
  have hp := primitive_LFunction_local_zero_poles_re_ge_single hq hχ σ β t hσ hβ hzero
  linarith

end Chen
