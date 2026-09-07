import ChenTheorem.Lemma6.StripGrowth
import ChenTheorem.Lemma6.DirichletEulerLogDerivative

namespace Chen

theorem norm_dirichletEulerFactor_le_prime {d p : ℕ} (χ : DirichletCharacter ℂ d)
    (hp : p.Prime) {s : ℂ} (hs : 0 ≤ s.re) : ‖dirichletEulerFactor χ p s‖ ≤ (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hterm : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [norm_mul, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < p), Complex.neg_re]
    have hpow : (p : ℝ) ^ (-s.re) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ p)
        (by linarith : -s.re ≤ 0)
    exact mul_le_one₀ (χ.norm_le_one p) (Real.rpow_nonneg (Nat.cast_nonneg p) _) hpow
  have h := norm_sub_le (1 : ℂ) (χ p * (p : ℂ) ^ (-s))
  rw [norm_one] at h
  exact h.trans (by linarith)

theorem norm_dirichletEulerProduct_le_level {d q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ d) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∏ p ∈ q.primeFactors, dirichletEulerFactor χ p s‖ ≤ (q : ℝ) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ p ∈ q.primeFactors, (p : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun p hp => norm_dirichletEulerFactor_le_prime χ (Nat.prime_of_mem_primeFactors hp) hs)
    _ ≤ q := by
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.prod_primeFactors_dvd q)

/-- A deliberately coarse uniform polynomial bound on the compact region
used by the Cauchy estimate in Siegel's argument. -/
theorem norm_nonprincipal_LFunction_compact_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (hs : (1 / 2 : ℝ) ≤ s.re) (hnorm : ‖s‖ ≤ 7 / 2) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 42 * (q : ℝ) ^ 3 := by
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hdne : χ.conductor ≠ 1 := fun h => hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  have hd : 2 ≤ χ.conductor := by have := χ.conductor_ne_zero; omega
  have hdq : χ.conductor ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hdR : (2 : ℝ) ≤ χ.conductor := by exact_mod_cast hd
  have hdqR : (χ.conductor : ℝ) ≤ q := by exact_mod_cast hdq
  have hqR : (2 : ℝ) ≤ q := hdR.trans hdqR
  have hprimitive : χ.primitiveCharacter ≠ 1 := by
    intro h
    have he := χ.changeLevel_primitiveCharacter
    rw [h, DirichletCharacter.changeLevel_one] at he
    exact hχ he.symm
  have he := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (s := s) (Or.inl hprimitive)
  rw [χ.changeLevel_primitiveCharacter] at he
  have hsqrt : Real.sqrt χ.conductor ≤ q := by
    have hsq := Real.sq_sqrt (Nat.cast_nonneg χ.conductor)
    have hmul := mul_nonneg (show 0 ≤ (χ.conductor : ℝ) - 1 by linarith)
      (Nat.cast_nonneg (α := ℝ) χ.conductor)
    nlinarith [Real.sqrt_nonneg χ.conductor]
  have hlog0 : 0 ≤ Real.log (2 * (χ.conductor : ℝ)) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2 * (χ.conductor : ℝ)) ≤ 2 * q :=
    (Real.log_le_self (by positivity)).trans (by linarith)
  have hbase : 3 * Real.sqrt χ.conductor * Real.log (2 * (χ.conductor : ℝ)) ≤ 6 * (q : ℝ) ^ 2 := by
    have hmul := mul_le_mul hsqrt hlog hlog0 (by linarith : (0 : ℝ) ≤ q)
    nlinarith
  have hratio : ‖s‖ / s.re ≤ (7 : ℝ) := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hp := norm_LFunction_le_of_re_pos χ.primitiveCharacter_isPrimitive hd (s := s) (by linarith)
  have hp' : ‖DirichletCharacter.LFunction χ.primitiveCharacter s‖ ≤ 42 * (q : ℝ) ^ 2 := by
    apply hp.trans
    calc
      _ = (3 * Real.sqrt χ.conductor * Real.log (2 * (χ.conductor : ℝ))) * (‖s‖ / s.re) := by ring
      _ ≤ (6 * (q : ℝ) ^ 2) * 7 :=
        mul_le_mul hbase hratio (div_nonneg (norm_nonneg _) (by linarith)) (by positivity)
      _ = _ := by ring
  rw [he, norm_mul]
  have heuler := norm_dirichletEulerProduct_le_level (q := q) χ.primitiveCharacter (s := s) (by linarith)
  calc
    _ ≤ (42 * (q : ℝ) ^ 2) * q := mul_le_mul hp' heuler (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Chen
