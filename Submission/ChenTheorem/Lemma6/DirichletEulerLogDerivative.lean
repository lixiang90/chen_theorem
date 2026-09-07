import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.DirichletCharacter.Bounds

set_option autoImplicit true

open Set Metric

namespace Chen

noncomputable def dirichletEulerFactor {d : ℕ} (χ : DirichletCharacter ℂ d)
    (p : ℕ) (s : ℂ) : ℂ := 1 - χ p * (p : ℂ) ^ (-s)

theorem norm_dirichletEulerTerm_le_inv {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ 1 / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [norm_mul, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < p), Complex.neg_re]
  calc
    _ ≤ 1 * (p : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (χ.norm_le_one p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ ≤ (p : ℝ) ^ (-1 : ℝ) := by
      rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = _ := by rw [Real.rpow_neg_one, one_div]

theorem norm_dirichletEulerTerm_le_half {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  apply (norm_dirichletEulerTerm_le_inv χ hp s hs).trans
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp)

theorem dirichletEulerFactor_ne_zero {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) : dirichletEulerFactor χ p s ≠ 0 := by
  have h := norm_dirichletEulerTerm_le_half χ hp s hs
  intro he
  have he' : χ p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp he).symm
  rw [he', norm_one] at h
  norm_num at h

theorem hasDerivAt_dirichletEulerFactor {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : p ≠ 0) (s : ℂ) :
    HasDerivAt (dirichletEulerFactor χ p)
      (χ p * (p : ℂ) ^ (-s) * Complex.log p) s := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hpow := (hasDerivAt_id s).neg.const_cpow (c := (p : ℂ)) (Or.inl hpC)
  have h := (hpow.const_mul (χ p)).const_sub 1
  change HasDerivAt (dirichletEulerFactor χ p)
    (-(χ p * ((p : ℂ) ^ (-s) * Complex.log p * (-1)))) s at h
  convert h using 1
  ring

theorem norm_deriv_dirichletEulerFactor {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : 2 ≤ p) (s : ℂ) :
    ‖deriv (dirichletEulerFactor χ p) s‖ = Real.log p * ‖χ p * (p : ℂ) ^ (-s)‖ := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p),
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith))]
  rw [(hasDerivAt_dirichletEulerFactor χ (by omega) s).deriv, norm_mul, hlog, mul_comm]

theorem norm_logDeriv_dirichletEulerFactor_le {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : 2 ≤ p) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖logDeriv (dirichletEulerFactor χ p) s‖ ≤ Real.log p := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hterm := norm_dirichletEulerTerm_le_half χ hp s hs
  have hden := norm_sub_norm_le (1 : ℂ) (χ p * (p : ℂ) ^ (-s))
  rw [norm_one] at hden
  change 1 - ‖χ p * (p : ℂ) ^ (-s)‖ ≤ ‖dirichletEulerFactor χ p s‖ at hden
  rw [logDeriv_apply, norm_div, norm_deriv_dirichletEulerFactor χ hp s]
  apply (div_le_iff₀ (norm_pos_iff.mpr (dirichletEulerFactor_ne_zero χ hp s hs))).mpr
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.log_nonneg (by linarith))

theorem sum_log_primeFactors_le_log (q : ℕ) (hq : 0 < q) :
    ∑ p ∈ q.primeFactors, Real.log (p : ℝ) ≤ Real.log q := by
  have hp : ∀ p ∈ q.primeFactors, (0 : ℝ) < p := by
    intro p hp
    exact_mod_cast Nat.pos_of_mem_primeFactors hp
  have hprod : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ q := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  rw [← Real.log_prod (fun p h => (hp p h).ne')]
  exact Real.log_le_log (Finset.prod_pos hp) hprod

theorem norm_logDeriv_dirichletEulerProduct_le {d : ℕ} (χ : DirichletCharacter ℂ d)
    (q : ℕ) (hq : 0 < q) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖logDeriv (fun z => ∏ p ∈ q.primeFactors, dirichletEulerFactor χ p z) s‖ ≤ Real.log q := by
  rw [logDeriv_prod (s := q.primeFactors) (f := fun p z => dirichletEulerFactor χ p z) (x := s)
    (fun p hp => dirichletEulerFactor_ne_zero χ (Nat.prime_of_mem_primeFactors hp).two_le s hs)
    (fun p hp => (hasDerivAt_dirichletEulerFactor χ (Nat.pos_of_mem_primeFactors hp).ne' s).differentiableAt)]
  apply (norm_sum_le _ _).trans
  apply le_trans _ (sum_log_primeFactors_le_log q hq)
  exact Finset.sum_le_sum (fun p hp => norm_logDeriv_dirichletEulerFactor_le χ
    (Nat.prime_of_mem_primeFactors hp).two_le s hs)

end Chen
