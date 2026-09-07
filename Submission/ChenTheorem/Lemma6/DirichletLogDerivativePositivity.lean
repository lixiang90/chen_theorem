import Submission.ChenTheorem.Lemma6.DirichletPhase

set_option autoImplicit true
open scoped LSeries.notation

namespace Chen

theorem vonMangoldt_three_four_one_term_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (n : ℕ) :
    0 ≤ (3 * LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) n +
      4 * LSeries.term (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + (t : ℂ) * Complex.I) n +
      LSeries.term (fun m => (χ ^ 2) m * (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n).re := by
  by_cases hn : n = 0
  · subst n
    simp
  let a : ℝ := ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)
  let z : ℂ := χ n * dirichletPhase n t
  have ha : 0 ≤ a := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hz : ‖z‖ ≤ 1 := by
    dsimp [z]
    rw [norm_mul, norm_dirichletPhase n hn t, mul_one]
    exact χ.norm_le_one n
  have hp := real_part_trigonometric_polynomial_nonneg z hz
  rw [vonMangoldt_term_real σ n hn, vonMangoldt_twist_term_phase χ σ t n hn,
    vonMangoldt_twist_term_phase (χ ^ 2) σ (2 * t) n hn,
    MulChar.pow_apply' χ (by norm_num : (2 : ℕ) ≠ 0), dirichletPhase_twice, ← mul_pow]
  change 0 ≤ (3 * (a : ℂ) + 4 * ((a : ℂ) * z) + (a : ℂ) * z ^ 2).re
  have he : (3 * (a : ℂ) + 4 * ((a : ℂ) * z) + (a : ℂ) * z ^ 2).re =
      a * (3 + 4 * z.re + (z ^ 2).re) := by simp [Complex.mul_re]; ring
  rw [he]
  exact mul_nonneg ha hp

theorem vonMangoldt_three_four_one_series_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ (3 * LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) +
      4 * LSeries (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + (t : ℂ) * Complex.I) +
      LSeries (fun m => (χ ^ 2) m * (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)).re := by
  have h1 := ArithmeticFunction.LSeriesSummable_vonMangoldt (show 1 < (σ : ℂ).re by simpa using hσ)
  have h2 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ
    (show 1 < ((σ : ℂ) + (t : ℂ) * Complex.I).re by simpa using hσ)
  have h3 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ ^ 2)
    (show 1 < ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I).re by simpa using hσ)
  change Summable (fun n => LSeries.term
    (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))
    ((σ : ℂ) + (t : ℂ) * Complex.I) n) at h2
  change Summable (fun n => LSeries.term
    (fun m => (χ ^ 2) m * (ArithmeticFunction.vonMangoldt m : ℂ))
    ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n) at h3
  have hsum := ((h1.mul_left (3 : ℂ)).add (h2.mul_left (4 : ℂ))).add h3
  have hn : 0 ≤ (∑' n, (3 * LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) n +
      4 * LSeries.term (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + (t : ℂ) * Complex.I) n +
      LSeries.term (fun m => (χ ^ 2) m * (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) n)).re := by
    rw [Complex.re_tsum hsum]
    exact tsum_nonneg (vonMangoldt_three_four_one_term_nonneg χ σ t)
  rw [((h1.mul_left (3 : ℂ)).add (h2.mul_left (4 : ℂ))).tsum_add h3,
    (h1.mul_left (3 : ℂ)).tsum_add (h2.mul_left (4 : ℂ)), tsum_mul_left, tsum_mul_left] at hn
  exact hn

theorem LSeries_twist_vonMangoldt_eq_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ)) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs

/-- The classical three-four-one inequality for logarithmic derivatives,
valid uniformly in every Dirichlet character on the half-plane of absolute convergence. -/
theorem Dirichlet_logDeriv_three_four_one_nonneg {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ (3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)) +
      4 * (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)) +
      (-deriv (DirichletCharacter.LFunction (χ ^ 2)) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I) /
        DirichletCharacter.LFunction (χ ^ 2) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I))).re := by
  have h := vonMangoldt_three_four_one_series_nonneg χ σ t hσ
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ),
    LSeries_twist_vonMangoldt_eq_LFunction χ _ (by simpa using hσ),
    LSeries_twist_vonMangoldt_eq_LFunction (χ ^ 2) _ (by simpa using hσ)] at h
  exact h

end Chen
