import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit true

namespace Chen

noncomputable def dirichletPhase (n : ℕ) (t : ℝ) : ℂ :=
  (n : ℂ) ^ (-((t : ℂ) * Complex.I))

theorem norm_dirichletPhase (n : ℕ) (hn : n ≠ 0) (t : ℝ) : ‖dirichletPhase n t‖ = 1 := by
  unfold dirichletPhase
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < n)]
  simp

theorem dirichletPhase_twice (n : ℕ) (t : ℝ) : dirichletPhase n (2 * t) = dirichletPhase n t ^ 2 := by
  unfold dirichletPhase
  rw [show -(((2 * t : ℝ) : ℂ) * Complex.I) = (-((t : ℂ) * Complex.I)) * (2 : ℕ) by push_cast; ring]
  exact Complex.cpow_mul_nat _ _ 2

theorem real_part_trigonometric_polynomial_nonneg (z : ℂ) (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hn := Complex.sq_norm z
  rw [Complex.normSq_apply] at hn
  rw [pow_two, Complex.mul_re]
  nlinarith [sq_nonneg (z.re + 1), norm_nonneg z]

/-- Separating the real decay from the vertical phase in a twisted von
Mangoldt series term. -/
theorem vonMangoldt_twist_term_phase {q : ℕ} (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    LSeries.term (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))
      ((σ : ℂ) + (t : ℂ) * Complex.I) n =
      ((ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        (χ n * dirichletPhase n t) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
    show -((σ : ℂ) + (t : ℂ) * Complex.I) = -(σ : ℂ) + -((t : ℂ) * Complex.I) by ring,
    Complex.cpow_add _ _ hnC]
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_neg, Complex.ofReal_natCast]
  unfold dirichletPhase
  ring

theorem vonMangoldt_term_real (σ : ℝ) (n : ℕ) (hn : n ≠ 0) :
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) n =
      ((ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero hn, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow (Nat.cast_nonneg n) σ, ← Complex.ofReal_div,
    Real.rpow_neg (Nat.cast_nonneg n)]
  congr 1

end Chen
