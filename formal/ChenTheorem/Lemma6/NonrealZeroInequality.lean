import ChenTheorem.Lemma6.NonprincipalLogDerivativeBound
import ChenTheorem.Lemma6.DirichletLogDerivativePositivity
import ChenTheorem.Lemma6.ZetaRealLogDerivativeBound

namespace Chen

theorem conductor_height_log_double_le {q : ℕ} (hq : 2 ≤ q) (t : ℝ) :
    Real.log ((q : ℝ) * (|2 * t| + 2)) ≤
      2 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < (q : ℝ) * (|t| + 2) := by positivity
  have hA : 2 ≤ (q : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ Real.log (((q : ℝ) * (|t| + 2)) ^ 2) := by
      apply Real.log_le_log (by positivity)
      nlinarith [sq_nonneg ((q : ℝ) * (|t| + 2) - 2)]
    _ = _ := by rw [Real.log_pow]; norm_num

theorem primitive_nonreal_zero_inequality {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ.IsPrimitive)
    (hχsq : χ ^ 2 ≠ 1) (σ β t C : ℝ) (hσ : 1 < σ) (hσ' : σ ≤ 3 / 2)
    (hβ : 7 / 8 < β)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (t : ℂ) * Complex.I) = 0)
    (hzeta : (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤
      1 / (σ - 1) + C) :
    4 / (σ - β) ≤ 3 / (σ - 1) + 3 * C +
      360002 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have h1 := primitive_LFunction_logDeriv_re_ge_single_zero hq hχ σ β t hσ hσ' hβ hzero
  have h2 := nonprincipal_LFunction_logDeriv_re_ge (χ ^ 2) hχsq σ (2 * t) hσ hσ'
  have h3 := Dirichlet_logDeriv_three_four_one_nonneg χ σ t hσ
  norm_num [Complex.add_re, Complex.mul_re, neg_div] at h3 hzeta
  have h4 := conductor_height_log_double_le hq t
  norm_num at h1 h2 h4 ⊢
  simp only [div_eq_mul_inv]
  linarith

end Chen
