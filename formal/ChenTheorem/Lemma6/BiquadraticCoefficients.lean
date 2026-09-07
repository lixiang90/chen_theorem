import Mathlib.NumberTheory.LSeries.Nonvanishing

open ArithmeticFunction
open scoped ComplexOrder

namespace Chen

theorem convolution_prime_power_congr {p : ℕ} (hp : p.Prime)
    {f₁ f₂ g₁ g₂ : ArithmeticFunction ℂ}
    (hf : ∀ k : ℕ, f₁ (p ^ k) = f₂ (p ^ k))
    (hg : ∀ k : ℕ, g₁ (p ^ k) = g₂ (p ^ k)) (k : ℕ) :
    (f₁ * g₁) (p ^ k) = (f₂ * g₂) (p ^ k) := by
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have he := (Nat.mem_divisorsAntidiagonal.mp hd).1
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp (show d.1 ∣ p ^ k from ⟨d.2, he.symm⟩)
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp
    (show d.2 ∣ p ^ k from ⟨d.1, by rw [mul_comm]; exact he.symm⟩)
  rw [hi, hj, hf i, hg j]

theorem charArithmetic_prime_power {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (k : ℕ) :
    toArithmeticFunction (χ ·) (p ^ k) = χ p ^ k := by
  simp [toArithmeticFunction, hp.ne_zero, map_pow]

theorem charArithmetic_prime_power_eq_one {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (h : χ p = 0) (k : ℕ) :
    toArithmeticFunction (χ ·) (p ^ k) = (1 : ArithmeticFunction ℂ) (p ^ k) := by
  rw [charArithmetic_prime_power χ hp, h]
  cases k with
  | zero => simp
  | succ k => simp [hp.ne_one]

theorem charArithmetic_prime_power_eq_zeta {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) (h : χ p = 1) (k : ℕ) :
    toArithmeticFunction (χ ·) (p ^ k) = (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ k) := by
  simp [charArithmetic_prime_power χ hp, h, hp.ne_zero]

/-- The Dirichlet coefficients of ζ(s)L(s,χ)L(s,ψ)L(s,χψ).
Multiplication in this definition is Dirichlet convolution. -/
noncomputable def biquadraticCoefficients {q : ℕ}
    (χ ψ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  χ.zetaMul * (toArithmeticFunction (ψ ·) * toArithmeticFunction ((χ * ψ) ·))

theorem biquadraticCoefficients_isMultiplicative {q : ℕ}
    (χ ψ : DirichletCharacter ℂ q) : (biquadraticCoefficients χ ψ).IsMultiplicative :=
  χ.isMultiplicative_zetaMul.mul ((DirichletCharacter.isMultiplicative_toArithmeticFunction ψ).mul
    (DirichletCharacter.isMultiplicative_toArithmeticFunction (χ * ψ)))

theorem convolution_nonneg {f g : ArithmeticFunction ℂ}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f * g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun d _ => mul_nonneg (hf d.1) (hg d.2)

theorem biquadraticCoefficients_prime_power_nonneg {q p : ℕ}
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (hp : p.Prime) (k : ℕ) : 0 ≤ biquadraticCoefficients χ ψ (p ^ k) := by
  let Z : ArithmeticFunction ℂ := ArithmeticFunction.zeta
  let A := toArithmeticFunction (χ ·)
  let B := toArithmeticFunction (ψ ·)
  let C := toArithmeticFunction ((χ * ψ) ·)
  have hc (v : ℂ) (hv : χ p * ψ p = v) (i : ℕ) : C (p ^ i) = v ^ i := by
    change toArithmeticFunction ((χ * ψ) ·) (p ^ i) = v ^ i
    rw [charArithmetic_prime_power (χ * ψ) hp, MulChar.mul_apply, hv]
  have hsχ : 0 ≤ (χ.zetaMul * χ.zetaMul) (p ^ k) :=
    convolution_nonneg (DirichletCharacter.zetaMul_nonneg hχ)
      (DirichletCharacter.zetaMul_nonneg hχ) _
  have hsψ : 0 ≤ (ψ.zetaMul * ψ.zetaMul) (p ^ k) :=
    convolution_nonneg (DirichletCharacter.zetaMul_nonneg hψ)
      (DirichletCharacter.zetaMul_nonneg hψ) _
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with ha | ha | ha
  · have hA := charArithmetic_prime_power_eq_one χ hp ha
    have hC := charArithmetic_prime_power_eq_one (χ * ψ) hp
      (by rw [MulChar.mul_apply, ha, zero_mul])
    have he := convolution_prime_power_congr hp
      (convolution_prime_power_congr hp (f₁ := Z) (f₂ := Z) (fun _ => rfl) hA)
      (convolution_prime_power_congr hp (f₁ := B) (f₂ := B) (fun _ => rfl) hC) k
    have he' : biquadraticCoefficients χ ψ (p ^ k) = ψ.zetaMul (p ^ k) := by
      simpa only [biquadraticCoefficients, DirichletCharacter.zetaMul, Z, B,
        mul_one] using he
    rw [he']
    exact DirichletCharacter.zetaMul_nonneg hψ _
  · have hA := charArithmetic_prime_power_eq_zeta χ hp ha
    have hC : ∀ i : ℕ, C (p ^ i) = B (p ^ i) := by
      intro i
      rw [hc (ψ p) (by rw [ha, one_mul]), charArithmetic_prime_power ψ hp]
    have he := convolution_prime_power_congr hp
      (convolution_prime_power_congr hp (f₁ := Z) (f₂ := Z) (fun _ => rfl) hA)
      (convolution_prime_power_congr hp (f₁ := B) (f₂ := B) (fun _ => rfl) hC) k
    have he' : biquadraticCoefficients χ ψ (p ^ k) =
        (ψ.zetaMul * ψ.zetaMul) (p ^ k) := by
      simpa only [biquadraticCoefficients, DirichletCharacter.zetaMul, Z, B, C,
        mul_assoc, mul_comm, mul_left_comm] using he
    rw [he']
    exact hsψ
  · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hψ p with hb | hb | hb
    · have hB := charArithmetic_prime_power_eq_one ψ hp hb
      have hC := charArithmetic_prime_power_eq_one (χ * ψ) hp
        (by rw [MulChar.mul_apply, hb, mul_zero])
      have he := convolution_prime_power_congr hp
        (f₁ := χ.zetaMul) (f₂ := χ.zetaMul) (fun _ => rfl)
        (convolution_prime_power_congr hp hB hC) k
      have he' : biquadraticCoefficients χ ψ (p ^ k) = χ.zetaMul (p ^ k) := by
        simpa only [biquadraticCoefficients, mul_one] using he
      rw [he']
      exact DirichletCharacter.zetaMul_nonneg hχ _
    · have hB := charArithmetic_prime_power_eq_zeta ψ hp hb
      have hC : ∀ i : ℕ, C (p ^ i) = A (p ^ i) := by
        intro i
        rw [hc (χ p) (by rw [hb, mul_one]), charArithmetic_prime_power χ hp]
      have he := convolution_prime_power_congr hp
        (f₁ := χ.zetaMul) (f₂ := χ.zetaMul) (fun _ => rfl)
        (convolution_prime_power_congr hp hB hC) k
      have he' : biquadraticCoefficients χ ψ (p ^ k) =
          (χ.zetaMul * χ.zetaMul) (p ^ k) := by
        simpa only [biquadraticCoefficients, DirichletCharacter.zetaMul, A, C] using he
      rw [he']
      exact hsχ
    · have hB : ∀ i : ℕ, B (p ^ i) = A (p ^ i) := by
        intro i
        rw [charArithmetic_prime_power ψ hp, charArithmetic_prime_power χ hp, ha, hb]
      have hC := charArithmetic_prime_power_eq_zeta (χ * ψ) hp
        (by rw [MulChar.mul_apply, ha, hb]; norm_num)
      have he := convolution_prime_power_congr hp
        (f₁ := χ.zetaMul) (f₂ := χ.zetaMul) (fun _ => rfl)
        (convolution_prime_power_congr hp hB hC) k
      have he' : biquadraticCoefficients χ ψ (p ^ k) =
          (χ.zetaMul * χ.zetaMul) (p ^ k) := by
        simpa only [biquadraticCoefficients, DirichletCharacter.zetaMul, A, B,
          mul_comm] using he
      rw [he']
      exact hsχ

/-- Positivity of the coefficients used in the classical Siegel argument. -/
theorem biquadraticCoefficients_nonneg {q : ℕ}
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hψ : ψ ^ 2 = 1)
    (n : ℕ) : 0 ≤ biquadraticCoefficients χ ψ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simpa only [(biquadraticCoefficients_isMultiplicative χ ψ).multiplicative_factorization _ hn]
      using! Finset.prod_nonneg fun p hp =>
        biquadraticCoefficients_prime_power_nonneg χ ψ hχ hψ (Nat.prime_of_mem_primeFactors hp) _

end Chen
