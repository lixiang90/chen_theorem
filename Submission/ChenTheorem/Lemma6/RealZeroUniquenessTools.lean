import Submission.ChenTheorem.Lemma6.RealCharacterZeroInequality

set_option autoImplicit true
open Set Metric

namespace Chen

theorem primitive_LFunction_logDeriv_re_ge_two_real_zeros {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive)
    (σ β₁ β₂ : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2)
    (hβ₁ : 15 / 16 < β₁) (hβ₂ : 15 / 16 < β₂) (hne : β₁ ≠ β₂)
    (hf₁ : DirichletCharacter.LFunction χ (β₁ : ℂ) = 0)
    (hf₂ : DirichletCharacter.LFunction χ (β₂ : ℂ) = 0) :
    1 / (σ - β₁) + 1 / (σ - β₂) - 60000 * Real.log ((q : ℝ) * 2) ≤
      (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re := by
  have hzero_le : ∀ β : ℝ, DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 := by
    intro β hb
    by_contra! hh
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inr (by intro he; have := congrArg Complex.re he; simp at this; linarith))
      (by simpa using hh.le)) hb
  let c := dirichletZeroDiskCenter 0
  let w₁ := (β₁ : ℂ) - c
  let w₂ := (β₂ : ℂ) - c
  let z := (σ : ℂ) - c
  have hw₁ : w₁ ∈ ball 0 (3 / 8) := by
    rw [mem_ball_zero_iff]
    simpa [w₁, c] using norm_near_real_zero_shift_lt hβ₁ (hzero_le β₁ hf₁) (t := 0) (by norm_num)
  have hw₂ : w₂ ∈ ball 0 (3 / 8) := by
    rw [mem_ball_zero_iff]
    simpa [w₂, c] using norm_near_real_zero_shift_lt hβ₂ (hzero_le β₂ hf₂) (t := 0) (by norm_num)
  have hf₁' : DirichletCharacter.LFunction χ (c + w₁) = 0 := by
    have he : c + w₁ = (β₁ : ℂ) := by dsimp [w₁]; ring
    rw [he]; exact hf₁
  have hf₂' : DirichletCharacter.LFunction χ (c + w₂) = 0 := by
    have he : c + w₂ = (β₂ : ℂ) := by dsimp [w₂]; ring
    rw [he]; exact hf₂
  have hne' : w₁ ≠ w₂ := by
    intro he
    have h := congrArg Complex.re he
    simp [w₁, w₂] at h
    exact hne (by linarith)
  have h0 : DirichletCharacter.LFunction χ (c + 0) ≠ 0 :=
    centered_LFunction_ne_zero_of_re_gt_neg_quarter χ 0 0 (by norm_num)
  have hp := pair_re_zero_poles_le_diskZeroPoleSum_re (κ := -(1 / 4 : ℝ))
    (by norm_num : (0 : ℝ) < 3 / 8) (primitive_centered_LFunction_analytic hq hχ 0) h0
    (fun u _ hu => centered_LFunction_ne_zero_of_re_gt_neg_quarter χ 0 u hu)
    (z := z) (by dsimp [z, c]; simp [dirichletZeroDiskCenter]; linarith)
    hw₁ hw₂ hf₁' hf₂' hne'
  have he₁ : z - w₁ = ((σ - β₁ : ℝ) : ℂ) := by dsimp [z, w₁]; push_cast; ring
  have he₂ : z - w₂ = ((σ - β₂ : ℝ) : ℂ) := by dsimp [z, w₂]; push_cast; ring
  rw [he₁, he₂, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_div,
    Complex.ofReal_re, Complex.ofReal_re] at hp
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
      (diskZeroPoleSum (fun w => DirichletCharacter.LFunction χ (c + w)) (3 / 8) z).re at hr
  linarith

theorem two_real_zero_gaps_contradiction {x y₁ y₂ D : ℝ} (hx : 0 < x)
    (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (h₁ : y₁ ≤ 9 * x / 8) (h₂ : y₂ ≤ 9 * x / 8)
    (hDx : D * x ≤ 1 / 4) (hi : 1 / y₁ + 1 / y₂ ≤ 1 / x + D) : False := by
  have hden : 0 < 9 * x := by positivity
  have hb₁ : 8 / (9 * x) ≤ 1 / y₁ := by
    apply (div_le_div_iff₀ hden hy₁).mpr
    nlinarith
  have hb₂ : 8 / (9 * x) ≤ 1 / y₂ := by
    apply (div_le_div_iff₀ hden hy₂).mpr
    nlinarith
  have hh : 16 / (9 * x) ≤ 1 / x + D := by
    calc
      _ = 8 / (9 * x) + 8 / (9 * x) := by ring
      _ ≤ 1 / y₁ + 1 / y₂ := add_le_add hb₁ hb₂
      _ ≤ _ := hi
  have hh' := (div_le_iff₀ hden).mp hh
  have he : (1 / x + D) * (9 * x) = 9 + 9 * (D * x) := by
    calc
      _ = 9 * (1 / x * x) + 9 * (D * x) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hx.ne', mul_one]
  rw [he] at hh'
  linarith

theorem exists_real_character_logDeriv_real_axis_bound :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ^ 2 = 1 → ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re ≤
        1 / (σ - 1) + C + Real.log q / 4 := by
  obtain ⟨δz, Cz, hδz, hCz, hzeta⟩ := exists_zeta_real_logDeriv_pole_bound
  obtain ⟨δp, Cp, hδp, hCp, hprincipal⟩ := exists_principal_complex_logDeriv_pole_bound
  refine ⟨min δz δp, (3 * Cz + Cp) / 4, lt_min hδz hδp, by positivity, ?_⟩
  intro q inst χ hsq σ hσ hσδ
  have hz : σ < 1 + δz := by linarith [min_le_left δz δp]
  have hp : ‖(σ : ℂ) - 1‖ < δp := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < σ - 1)]
    linarith [min_le_right δz δp]
  have h := real_character_logDeriv_real_axis_le χ hsq σ Cz Cp hσ (hzeta σ hσ hz)
    (hprincipal q (σ : ℂ) (by simpa using hσ) hp)
  linarith

end Chen
