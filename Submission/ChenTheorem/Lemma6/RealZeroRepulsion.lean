import Submission.ChenTheorem.Lemma6.BiquadraticTruncation
import Submission.ChenTheorem.Lemma6.NonprincipalSmallPowerDerivative

set_option autoImplicit true
namespace Chen

/-- Quantitative repulsion between zeros belonging to two distinct real characters
of a common level. The radius and constant depend only on the chosen exponent. -/
theorem exists_real_zero_repulsion_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ r A : ℝ, 0 < r ∧ 0 < A ∧ ∀ (q : ℕ) [NeZero q]
      (χ ψ : DirichletCharacter ℂ q), 2 ≤ q → χ ≠ 1 → ψ ≠ 1 → χ * ψ ≠ 1 →
      χ ^ 2 = 1 → ψ ^ 2 = 1 → ∀ β₁ β₂ : ℝ,
      7 / 8 < β₁ → β₁ < 1 → DirichletCharacter.LFunction χ (β₁ : ℂ) = 0 →
      1 - r ≤ β₂ → β₂ ≤ 1 → DirichletCharacter.LFunction ψ (β₂ : ℂ) = 0 →
      (1 - β₁) / (A * (q : ℝ) ^ (36 * (1 - β₁) + 3 * ε)) ≤ 1 - β₂ := by
  obtain ⟨K, hK, hOne⟩ := exists_nonprincipal_LFunction_one_small_power hε
  obtain ⟨r, D, hr, hD, hZero⟩ := exists_nonprincipal_one_bound_of_real_zero hε
  let A : ℝ := 2 * siegelTruncationConstant * K ^ 2 * D
  have hC := siegelTruncationConstant_pos
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨r, A, hr, hA, ?_⟩
  intro q inst χ ψ hq hχ hψ hχψ hχsq hψsq β₁ β₂ hβ₁ hβ₁' hz₁ hβ₂ hβ₂' hz₂
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hgap₂ : 0 ≤ 1 - β₂ := sub_nonneg.mpr hβ₂'
  have h1 := hOne q χ hq hχ
  have h2 := hZero q ψ hq hψ β₂ hβ₂ hβ₂' hz₂
  have h3 := hOne q (χ * ψ) hq hχψ
  have hres : ‖biquadraticResidue χ ψ‖ ≤ K ^ 2 * D * (q : ℝ) ^ (3 * ε) * (1 - β₂) := by
    simp only [biquadraticResidue, biquadraticHolomorphicFactor, norm_mul]
    calc
      _ ≤ (K * (q : ℝ) ^ ε) * (D * (q : ℝ) ^ ε * (1 - β₂)) * (K * (q : ℝ) ^ ε) :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _) (by positivity)
      _ = K ^ 2 * D * ((q : ℝ) ^ ε) ^ 3 * (1 - β₂) := by ring
      _ = _ := by simp only [← Real.rpow_mul_natCast hq0.le, Nat.cast_ofNat, mul_comm ε (3 : ℝ)]
  have hlower := biquadraticResidue_lower_of_real_zero hq χ ψ hχ hψ hχψ hχsq hψsq β₁ hβ₁ hβ₁' hz₁
  have hresre := (Complex.re_le_norm (biquadraticResidue χ ψ)).trans hres
  have hpos : 0 < 2 * siegelTruncationConstant * (q : ℝ) ^ (36 * (1 - β₁)) := by positivity
  have hprod := (div_le_iff₀ hpos).mp (hlower.trans hresre)
  have hid : (K ^ 2 * D * (q : ℝ) ^ (3 * ε) * (1 - β₂)) *
      (2 * siegelTruncationConstant * (q : ℝ) ^ (36 * (1 - β₁))) =
      (1 - β₂) * (A * (q : ℝ) ^ (36 * (1 - β₁) + 3 * ε)) := by
    rw [Real.rpow_add hq0]
    dsimp [A]
    ring
  rw [hid] at hprod
  exact (div_le_iff₀ (by positivity : 0 < A * (q : ℝ) ^ (36 * (1 - β₁) + 3 * ε))).mpr hprod

end Chen
