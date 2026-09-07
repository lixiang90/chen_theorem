import Submission.ChenTheorem.Lemma6.DirichletEulerLogDerivative
import Mathlib.NumberTheory.LSeries.Nonvanishing

set_option autoImplicit true

namespace Chen

theorem dirichletEulerFactor_ne_zero_of_re_pos {d p : ℕ}
    (χ : DirichletCharacter ℂ d) (hp : 2 ≤ p) (s : ℂ) (hs : 0 < s.re) :
    dirichletEulerFactor χ p s ≠ 0 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hnorm : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < p), Complex.neg_re]
    calc
      _ ≤ 1 * (p : ℝ) ^ (-s.re) := mul_le_mul_of_nonneg_right
        (χ.norm_le_one p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hpR (neg_neg_of_pos hs)
  intro he
  have he' : χ p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp he).symm
  simp [he'] at hnorm

theorem LFunction_changeLevel_zero_iff {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction (χ.changeLevel hdq) s = 0 ↔
      DirichletCharacter.LFunction χ s = 0 := by
  rw [DirichletCharacter.LFunction_changeLevel hdq χ (Or.inl hχ)]
  have hp : (∏ p ∈ q.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact dirichletEulerFactor_ne_zero_of_re_pos χ (Nat.prime_of_mem_primeFactors hp).two_le s hs
  simp only [mul_eq_zero, hp, or_false]

theorem real_character_changeLevel {d q : ℕ} (hdq : d ∣ q)
    (χ : DirichletCharacter ℂ d) (hχ : χ ^ 2 = 1) :
    (χ.changeLevel hdq) ^ 2 = 1 := by
  rw [← map_pow, hχ, map_one]

theorem real_character_eq_of_mul_eq_one {q : ℕ}
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hprod : χ * ψ = 1) : ψ = χ := by
  calc
    ψ = (χ * χ) * ψ := by rw [← pow_two, hχ, one_mul]
    _ = χ := by rw [mul_assoc, hprod, mul_one]

theorem exists_nonprincipal_one_nonvanishing_ball {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℂ, ‖s - 1‖ < η → DirichletCharacter.LFunction χ s ≠ 0 := by
  have h := (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt.eventually_ne
    (DirichletCharacter.LFunction_apply_one_ne_zero hχ)
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp h
  exact ⟨η, hη, fun s hs => hball (by simpa only [Metric.mem_ball, dist_eq_norm] using hs)⟩

end Chen
