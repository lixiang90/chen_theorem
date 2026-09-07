import Submission.ChenTheorem.Lemma6.BiquadraticTaylor
import Submission.ChenTheorem.Lemma6.NonprincipalCompactGrowth

set_option autoImplicit true
namespace Chen

theorem norm_biquadraticHolomorphicFactor_compact_le {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) (hnorm : ‖s‖ ≤ 7 / 2) :
    ‖biquadraticHolomorphicFactor χ ψ s‖ ≤ (42 * (q : ℝ) ^ 3) ^ 3 := by
  have h1 := norm_nonprincipal_LFunction_compact_le χ hχ hs hnorm
  have h2 := norm_nonprincipal_LFunction_compact_le ψ hψ hs hnorm
  have h3 := norm_nonprincipal_LFunction_compact_le (χ * ψ) hχψ hs hnorm
  simp only [biquadraticHolomorphicFactor, norm_mul]
  calc
    _ ≤ (42 * (q : ℝ) ^ 3) * (42 * (q : ℝ) ^ 3) * (42 * (q : ℝ) ^ 3) :=
      mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem norm_biquadraticResidue_le {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    ‖biquadraticResidue χ ψ‖ ≤ (42 * (q : ℝ) ^ 3) ^ 3 :=
  norm_biquadraticHolomorphicFactor_compact_le χ ψ hχ hψ hχψ (s := 1) (by norm_num) (by norm_num)

/-- The actual Taylor coefficients satisfy a uniform conductor-polynomial bound;
no growth assumptions remain in this statement. -/
theorem norm_biquadraticTaylor_sub_residue_le_level {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) (n : ℕ) :
    ‖backwardTaylorCoeff (biquadraticLFunction χ ψ) 2 n - biquadraticResidue χ ψ‖ ≤
      (12 * (42 * (q : ℝ) ^ 3) ^ 3) * (2 / 3 : ℝ) ^ n := by
  apply norm_biquadraticTaylor_sub_residue_le χ ψ hχ hψ hχψ (by positivity)
  · intro s hs
    obtain ⟨hre, hnorm, _⟩ := siegel_circle_geometry hs
    exact norm_biquadraticHolomorphicFactor_compact_le χ ψ hχ hψ hχψ hre hnorm
  · exact norm_biquadraticResidue_le χ ψ hχ hψ hχψ

end Chen
