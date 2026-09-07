import Submission.ChenTheorem.Lemma6.RealCharacterConjugation
import Submission.ChenTheorem.Analysis.ZeroPoleSubsetRealPart

set_option autoImplicit true
open Set Metric ComplexConjugate

namespace Chen

theorem real_conjugate_pole_pair_re (σ β t : ℝ) :
    (1 / ((σ : ℂ) - ((β : ℂ) + (t : ℂ) * Complex.I))).re +
    (1 / ((σ : ℂ) - ((β : ℂ) - (t : ℂ) * Complex.I))).re =
      2 * (σ - β) / ((σ - β) ^ 2 + t ^ 2) := by
  simp only [Complex.div_re, Complex.one_re, Complex.one_im, Complex.normSq_apply,
    Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im,
    Complex.mul_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add, mul_one,
    zero_sub, neg_neg, neg_mul_neg, zero_div, one_mul]
  ring

theorem norm_near_real_zero_shift_lt {β t : ℝ} (hβ : 15 / 16 < β) (hβ' : β ≤ 1)
    (ht : |t| ≤ 1 / 32) :
    ‖(β : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter 0‖ < 3 / 8 := by
  have he : (β : ℂ) + (t : ℂ) * Complex.I - dirichletZeroDiskCenter 0 =
      ((β - 5 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    simp [dirichletZeroDiskCenter]; ring
  rw [he]
  apply lt_of_le_of_lt (norm_add_le _ _) _
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, abs_of_neg (by linarith : β - 5 / 4 < 0)]
  linarith

/-- A nonreal zero of a primitive real character near 1 contributes together
with its conjugate when the logarithmic derivative is evaluated on the real axis. -/
theorem primitive_real_LFunction_logDeriv_re_ge_zero_pair {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1)
    (σ β t : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) (hβ : 15 / 16 < β)
    (ht : |t| ≤ 1 / 32) (htne : t ≠ 0)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (t : ℂ) * Complex.I) = 0) :
    2 * (σ - β) / ((σ - β) ^ 2 + t ^ 2) - 60000 * Real.log ((q : ℝ) * 2) ≤
      (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re := by
  have hχne : χ ≠ 1 := by
    intro he
    have hcond := DirichletCharacter.eq_one_iff_conductor_eq_one.mp he
    rw [DirichletCharacter.isPrimitive_def] at hχ
    omega
  have hβ' : β ≤ 1 := by
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; have := congrArg Complex.re he; simp at this; linarith))
      (by simpa using hh.le)) hzero
  let c := dirichletZeroDiskCenter 0
  let w₁ := (β : ℂ) + (t : ℂ) * Complex.I - c
  let w₂ := (β : ℂ) - (t : ℂ) * Complex.I - c
  let z := (σ : ℂ) - c
  have hw₁ : w₁ ∈ ball 0 (3 / 8) := by
    rw [mem_ball_zero_iff]
    exact norm_near_real_zero_shift_lt hβ hβ' ht
  have hw₂ : w₂ ∈ ball 0 (3 / 8) := by
    rw [mem_ball_zero_iff]
    convert norm_near_real_zero_shift_lt hβ hβ' (t := -t) (by simpa using ht) using 1
    simp [w₂, c, sub_eq_add_neg]
  have hf₁ : DirichletCharacter.LFunction χ (c + w₁) = 0 := by
    have he : c + w₁ = (β : ℂ) + (t : ℂ) * Complex.I := by dsimp [w₁]; ring
    rw [he]; exact hzero
  have hf₂ : DirichletCharacter.LFunction χ (c + w₂) = 0 := by
    have he : c + w₂ = conj ((β : ℂ) + (t : ℂ) * Complex.I) := by
      dsimp [w₂]; simp; ring
    rw [he]
    exact real_character_conjugate_zero χ hχne hsq hzero
  have hne : w₁ ≠ w₂ := by
    intro he
    have him := congrArg Complex.im he
    simp [w₁, w₂, c, dirichletZeroDiskCenter] at him
    exact htne (by linarith)
  have h0 : DirichletCharacter.LFunction χ (c + 0) ≠ 0 := by
    exact centered_LFunction_ne_zero_of_re_gt_neg_quarter χ 0 0 (by norm_num)
  have hp := pair_re_zero_poles_le_diskZeroPoleSum_re (κ := -(1 / 4 : ℝ))
    (by norm_num : (0 : ℝ) < 3 / 8) (primitive_centered_LFunction_analytic hq hχ 0) h0
    (fun u _ hu => centered_LFunction_ne_zero_of_re_gt_neg_quarter χ 0 u hu)
    (z := z) (by dsimp [z, c]; simp [dirichletZeroDiskCenter]; linarith)
    hw₁ hw₂ hf₁ hf₂ hne
  have he₁ : z - w₁ = (σ : ℂ) - ((β : ℂ) + (t : ℂ) * Complex.I) := by dsimp [z, w₁]; ring
  have he₂ : z - w₂ = (σ : ℂ) - ((β : ℂ) - (t : ℂ) * Complex.I) := by dsimp [z, w₂]; ring
  rw [he₁, he₂, real_conjugate_pole_pair_re] at hp
  have hsne : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχne) (by simpa using hσ.le)
  have hb := norm_LFunction_logDeriv_sub_local_zero_poles_le_log hq hχ 0 (σ : ℂ)
    (by simpa using norm_line_point_sub_dirichletZeroDiskCenter_le hσ hσ' 0) hsne
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  simp only [Complex.sub_re, abs_zero, zero_add] at hr
  change -(60000 * Real.log ((q : ℝ) * 2)) ≤
    (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re -
      (diskZeroPoleSum (fun w => DirichletCharacter.LFunction χ (c + w)) (3 / 8) z).re at hr
  linarith

end Chen
