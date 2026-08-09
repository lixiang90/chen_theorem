import ChenTheorem.LargeSieve.Character
import ChenTheorem.Lemma6.DivisorSquareWeighted
import ChenTheorem.Lemma6.MollifierSquare

/-!
# The `C_H` polynomial and the dyadic character large sieve

This file packages the exact large-sieve step used in equation (14) of
Chen's proof.  A complex phase of norm at most one represents the factor
`n⁻ⁱᵗ`; the remaining `1 / n` supplies the real part `Re ω ≥ 1`.
-/

open scoped ArithmeticFunction.Moebius Classical

namespace Chen

/-- Complex norm form of `|j_H(n)| ≤ τ(n)`. -/
theorem norm_lemma6MollifierSquareCoeff_le_card (H n : ℕ) :
    ‖(lemma6MollifierSquareCoeff H n : ℂ)‖ ≤
      (n.divisorsAntidiagonal.card : ℝ) := by
  rw [Complex.norm_intCast]
  exact_mod_cast abs_lemma6MollifierSquareCoeff_le_card H n

/-- Pointwise coefficient estimate at `Re s ≥ 1/2` for equation (15). -/
theorem lemma6_mollifierSquare_weighted_coeff_norm_sq_le
    {H n : ℕ} (u : ℕ → ℂ)
    (hu : ‖u n‖ ^ 2 ≤ (n : ℝ)⁻¹) :
    ‖(lemma6MollifierSquareCoeff H n : ℂ) * u n‖ ^ 2 ≤
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
  have hcoeff :
      ‖(lemma6MollifierSquareCoeff H n : ℂ)‖ ^ 2 ≤
        (n.divisorsAntidiagonal.card : ℝ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2
      (norm_lemma6MollifierSquareCoeff_le_card H n)
  rw [norm_mul, mul_pow]
  calc
    ‖(lemma6MollifierSquareCoeff H n : ℂ)‖ ^ 2 * ‖u n‖ ^ 2 ≤
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 * (n : ℝ)⁻¹ :=
        mul_le_mul hcoeff hu (sq_nonneg _) (by positivity)
    _ = (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
      rw [div_eq_mul_inv]

/-- The raw character-large-sieve estimate for `S(H,s,χ)^2`. -/
theorem lemma6_mollifierSquare_large_sieve :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q H : ℕ) (u : ℕ → ℂ),
        1 ≤ D → D ≤ Q →
        (∀ n ∈ Finset.Icc 1 (H * H), ‖u n‖ ^ 2 ≤ (n : ℝ)⁻¹) →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖∑ n ∈ Finset.Icc 1 (H * H),
                ((lemma6MollifierSquareCoeff H n : ℂ) * u n) * χ n‖ ^ 2
              else 0) ≤
          C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
            ∑ n ∈ Finset.Icc 1 (H * H),
              (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
  rcases LargeSieve.large_sieve_character_dyadic with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q H u hD hDQ hu
  let a : ℕ → ℂ := fun n => (lemma6MollifierSquareCoeff H n : ℂ) * u n
  have hinterval :
      Finset.Ioc 0 (H * H) = Finset.Icc 1 (H * H) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hsieve := hlarge D Q 0 (H * H) a hD hDQ
  simp only [zero_add, hinterval, a] at hsieve
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Icc 1 (H * H),
            ((lemma6MollifierSquareCoeff H n : ℂ) * u n) * χ n‖ ^ 2
          else 0) ≤
      C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Icc 1 (H * H),
          ‖(lemma6MollifierSquareCoeff H n : ℂ) * u n‖ ^ 2 := hsieve
    _ ≤ C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Icc 1 (H * H),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro n hn
        exact lemma6_mollifierSquare_weighted_coeff_norm_sq_le u (hu n hn)
      · positivity

/-- Equation (15): the fourth moment of the truncated Möbius polynomial,
after expanding its square and applying the dyadic character large sieve. -/
theorem lemma6_mollifierSquare_fourthMoment :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q H : ℕ) (u : ℕ → ℂ),
        1 ≤ D → D ≤ Q → 2 ≤ H →
        (∀ n ∈ Finset.Icc 1 (H * H), ‖u n‖ ^ 2 ≤ (n : ℝ)⁻¹) →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖∑ n ∈ Finset.Icc 1 (H * H),
                ((lemma6MollifierSquareCoeff H n : ℂ) * u n) * χ n‖ ^ 2
              else 0) ≤
          C * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
            (Real.log ((H * H : ℕ) : ℝ)) ^ 4 := by
  rcases lemma6_mollifierSquare_large_sieve with ⟨A, hA, hlarge⟩
  rcases lemma6_divisorSquare_over_n_le_log_four with ⟨B, hB, hdivisor⟩
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro D Q H u hD hDQ hH hu
  have hHH : 2 ≤ H * H := by nlinarith
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Icc 1 (H * H),
            ((lemma6MollifierSquareCoeff H n : ℂ) * u n) * χ n‖ ^ 2
          else 0) ≤
      A * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Icc 1 (H * H),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) :=
      hlarge D Q H u hD hDQ hu
    _ ≤ A * ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
        (B * (Real.log ((H * H : ℕ) : ℝ)) ^ 4) := by
      apply mul_le_mul_of_nonneg_left (hdivisor (H * H) hHH)
      positivity
    _ = (A * B) *
        ((Q : ℝ) + ((H * H : ℕ) : ℝ) / (D : ℝ)) *
        (Real.log ((H * H : ℕ) : ℝ)) ^ 4 := by ring

/-- The complex norm of `C_H(n)` is bounded by the cardinality form of
`τ(n)` for `n ≠ 1`. -/
theorem norm_lemma6MollifierCoeff_le_card
    {H n : ℕ} (hn : n ≠ 1) :
    ‖(lemma6MollifierCoeff H n : ℂ)‖ ≤
      (n.divisorsAntidiagonal.card : ℝ) := by
  rw [Complex.norm_intCast]
  exact_mod_cast abs_lemma6MollifierCoeff_le_card (H := H) hn

/-- Pointwise square-norm estimate for the coefficients to which the large
sieve is applied in equation (14). -/
theorem lemma6_weighted_mollifierCoeff_norm_sq_le
    {H M N n : ℕ} (hM : 1 ≤ M) (hn : n ∈ Finset.Ioc M (M + N))
    (u : ℕ → ℂ) (hu : ‖u n‖ ≤ 1) :
    ‖(lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)‖ ^ 2 ≤
      (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
  have hnrange := Finset.mem_Ioc.mp hn
  have hn1 : n ≠ 1 := by omega
  have hnposNat : 0 < n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hnum :
      ‖(lemma6MollifierCoeff H n : ℂ)‖ * ‖u n‖ ≤
        (n.divisorsAntidiagonal.card : ℝ) := by
    calc
      ‖(lemma6MollifierCoeff H n : ℂ)‖ * ‖u n‖ ≤
          ‖(lemma6MollifierCoeff H n : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left hu (norm_nonneg _)
      _ = ‖(lemma6MollifierCoeff H n : ℂ)‖ := by ring
      _ ≤ (n.divisorsAntidiagonal.card : ℝ) :=
        norm_lemma6MollifierCoeff_le_card hn1
  have hquot :
      ‖(lemma6MollifierCoeff H n : ℂ)‖ * ‖u n‖ / (n : ℝ) ≤
        (n.divisorsAntidiagonal.card : ℝ) / (n : ℝ) :=
    div_le_div_of_nonneg_right hnum hnpos.le
  rw [norm_div, norm_mul, Complex.norm_natCast, ← div_pow]
  exact (sq_le_sq₀ (by positivity) (by positivity)).2 hquot

/-- Equation (14)'s character-large-sieve input for a dyadic interval.

The phase `u` may depend on the spectral parameter and only needs norm at
most one.  The conclusion is deliberately left in terms of the finite
`τ(n)² / n²` sum; the elementary divisor-sum estimate is a separate step. -/
theorem lemma6_mollifier_large_sieve :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M N H : ℕ) (u : ℕ → ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ M →
        (∀ n ∈ Finset.Ioc M (M + N), ‖u n‖ ≤ 1) →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖∑ n ∈ Finset.Ioc M (M + N),
                ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
              else 0) ≤
          C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
            ∑ n ∈ Finset.Ioc M (M + N),
              (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
  rcases LargeSieve.large_sieve_character_dyadic with ⟨C, hC, hlarge⟩
  refine ⟨C, hC, ?_⟩
  intro D Q M N H u hD hDQ hM hu
  let a : ℕ → ℂ := fun n =>
    (lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Ioc M (M + N),
            ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
          else 0) ≤
      C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
      exact hlarge D Q M N a hD hDQ
    _ ≤ C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Ioc M (M + N),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro n hn
        exact lemma6_weighted_mollifierCoeff_norm_sq_le hM hn u (hu n hn)
      · positivity

/-- Equation (14), conditional only on the elementary divisor-square mean:
the character large sieve and the `C_H` coefficient bound combine to give
the required weighted dyadic estimate. -/
theorem lemma6_mollifier_large_sieve_of_divisorSquareMean
    (hmean : Lemma6DivisorSquareMean) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M N H : ℕ) (u : ℕ → ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ M → 2 ≤ M + N →
        (∀ n ∈ Finset.Ioc M (M + N), ‖u n‖ ≤ 1) →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖∑ n ∈ Finset.Ioc M (M + N),
                ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
              else 0) ≤
          C * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
            ((M + N : ℕ) : ℝ) *
            (Real.log ((M + N : ℕ) : ℝ)) ^ 3 /
            (M : ℝ) ^ 2 := by
  rcases lemma6_mollifier_large_sieve with ⟨A, hA, hlarge⟩
  rcases lemma6_divisorSquare_weighted_Ioc_le hmean with
    ⟨B, hB, hweighted⟩
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro D Q M N H u hD hDQ hM hMN hu
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Ioc M (M + N),
            ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
          else 0) ≤
      A * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
        ∑ n ∈ Finset.Ioc M (M + N),
          (n.divisorsAntidiagonal.card : ℝ) ^ 2 / (n : ℝ) ^ 2 :=
      hlarge D Q M N H u hD hDQ hM hu
    _ ≤ A * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
        (B * ((M + N : ℕ) : ℝ) *
          (Real.log ((M + N : ℕ) : ℝ)) ^ 3 /
          (M : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left (hweighted M N hM hMN)
      positivity
    _ = (A * B) * ((Q : ℝ) + (N : ℝ) / (D : ℝ)) *
        ((M + N : ℕ) : ℝ) *
        (Real.log ((M + N : ℕ) : ℝ)) ^ 3 /
        (M : ℝ) ^ 2 := by ring

/-- The exact `(Q / M + 1 / D) log(2M)^3` dyadic shape used on the right
of equation (14). -/
theorem lemma6_mollifier_large_sieve_dyadic_of_divisorSquareMean
    (hmean : Lemma6DivisorSquareMean) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M H : ℕ) (u : ℕ → ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ M →
        (∀ n ∈ Finset.Ioc M (M + M), ‖u n‖ ≤ 1) →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖∑ n ∈ Finset.Ioc M (M + M),
                ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
              else 0) ≤
          C * ((Q : ℝ) / (M : ℝ) + (D : ℝ)⁻¹) *
            (Real.log ((M + M : ℕ) : ℝ)) ^ 3 := by
  rcases lemma6_mollifier_large_sieve_of_divisorSquareMean hmean with
    ⟨A, hA, hlarge⟩
  refine ⟨2 * A, by positivity, ?_⟩
  intro D Q M H u hD hDQ hM hu
  have hMN : 2 ≤ M + M := by omega
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  calc
    ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
        (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
          ‖∑ n ∈ Finset.Ioc M (M + M),
            ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
          else 0) ≤
      A * ((Q : ℝ) + (M : ℝ) / (D : ℝ)) *
        ((M + M : ℕ) : ℝ) *
        (Real.log ((M + M : ℕ) : ℝ)) ^ 3 /
        (M : ℝ) ^ 2 :=
      hlarge D Q M M H u hD hDQ hM hMN hu
    _ = (2 * A) * ((Q : ℝ) / (M : ℝ) + (D : ℝ)⁻¹) *
        (Real.log ((M + M : ℕ) : ℝ)) ^ 3 := by
      norm_num only [Nat.cast_add]
      field_simp
      ring

/-- Unconditional dyadic `(Q / M + 1 / D) log(2M)^3` form of equation (14). -/
theorem lemma6_mollifier_large_sieve_dyadic :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D Q M H : ℕ) (u : ℕ → ℂ),
        1 ≤ D → D ≤ Q → 1 ≤ M →
        (∀ n ∈ Finset.Ioc M (M + M), ‖u n‖ ≤ 1) →
        ∑ q ∈ Finset.Ioc D Q, (q.totient : ℝ)⁻¹ *
            (∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then
              ‖∑ n ∈ Finset.Ioc M (M + M),
                ((lemma6MollifierCoeff H n : ℂ) * u n / (n : ℂ)) * χ n‖ ^ 2
              else 0) ≤
          C * ((Q : ℝ) / (M : ℝ) + (D : ℝ)⁻¹) *
            (Real.log ((M + M : ℕ) : ℝ)) ^ 3 :=
  lemma6_mollifier_large_sieve_dyadic_of_divisorSquareMean
    lemma6_divisorSquareMean

end Chen
