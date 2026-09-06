import ChenTheorem.Lemma6.PrincipalLogDerivativeBound
import ChenTheorem.Lemma6.RealCharacterZeroPair
import ChenTheorem.Lemma6.DirichletLogDerivativePositivity

namespace Chen

theorem principal_logDeriv_re_ge_of_pole_bound {q : ℕ} [NeZero q]
    (s : ℂ) (C : ℝ)
    (hb : ‖logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s +
      (s - 1)⁻¹‖ ≤ C + Real.log q) :
    -((s - 1)⁻¹).re - C - Real.log q ≤
      (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s).re := by
  have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
  rw [Complex.add_re] at h
  linarith

theorem primitive_real_zero_inequality {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1)
    (σ β t Cz Cp : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2) (hβ : 7 / 8 < β)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (t : ℂ) * Complex.I) = 0)
    (hzeta : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + Cz)
    (hprincipal : ‖logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
      ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) +
      ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I - 1)⁻¹‖ ≤ Cp + Real.log q) :
    4 / (σ - β) ≤ 3 / (σ - 1) +
      (((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I - 1)⁻¹).re +
      3 * Cz + Cp + 240000 * Real.log ((q : ℝ) * (|t| + 2)) + Real.log q := by
  have h1 := primitive_LFunction_logDeriv_re_ge_single_zero hq hχ σ β t hσ hσ' hβ hzero
  have h2 := principal_logDeriv_re_ge_of_pole_bound _ Cp hprincipal
  have h3 := Dirichlet_logDeriv_three_four_one_nonneg χ σ t hσ
  rw [hsq] at h3
  simp only [logDeriv_apply] at h2
  norm_num [Complex.add_re, Complex.mul_re, neg_div] at h3 hzeta
  norm_num at h1 h2 ⊢
  simp only [div_eq_mul_inv] at h1 h2 h3 hzeta ⊢
  linarith

theorem real_character_logDeriv_real_axis_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (σ Cz Cp : ℝ) (hσ : 1 < σ)
    (hzeta : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + Cz)
    (hprincipal : ‖logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
      (σ : ℂ) + ((σ : ℂ) - 1)⁻¹‖ ≤ Cp + Real.log q) :
    (logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re ≤
      1 / (σ - 1) + (3 * Cz + Cp + Real.log q) / 4 := by
  have h2 := principal_logDeriv_re_ge_of_pole_bound (σ : ℂ) Cp hprincipal
  have h3 := Dirichlet_logDeriv_three_four_one_nonneg χ σ 0 hσ
  rw [hsq] at h3
  have he : (((σ : ℂ) - 1)⁻¹).re = 1 / (σ - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  rw [he] at h2
  simp only [logDeriv_apply] at h2 ⊢
  norm_num [Complex.add_re, Complex.mul_re, neg_div] at h3 hzeta
  norm_num at h2 ⊢
  simp only [div_eq_mul_inv] at h2 h3 hzeta ⊢
  norm_num only
  linarith

end Chen
