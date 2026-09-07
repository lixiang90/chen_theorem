import ChenTheorem.Lemma6.BiquadraticLSeries
import ChenTheorem.Analysis.ZetaRegularPart

namespace Chen

noncomputable def biquadraticHolomorphicFactor {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction ψ s *
    DirichletCharacter.LFunction (χ * ψ) s

noncomputable def biquadraticResidue {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) : ℂ := biquadraticHolomorphicFactor χ ψ 1

noncomputable def biquadraticRegularPart {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  regularizedZetaMul (biquadraticHolomorphicFactor χ ψ)

theorem differentiable_biquadraticHolomorphicFactor {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    Differentiable ℂ (biquadraticHolomorphicFactor χ ψ) :=
  ((DirichletCharacter.differentiable_LFunction hχ).mul
    (DirichletCharacter.differentiable_LFunction hψ)).mul
      (DirichletCharacter.differentiable_LFunction hχψ)

theorem differentiable_biquadraticRegularPart {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    Differentiable ℂ (biquadraticRegularPart χ ψ) :=
  differentiable_regularizedZetaMul
    (differentiable_biquadraticHolomorphicFactor χ ψ hχ hψ hχψ)

theorem biquadraticRegularPart_eq {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    biquadraticRegularPart χ ψ s = biquadraticLFunction χ ψ s - biquadraticResidue χ ψ / (s - 1) := by
  rw [biquadraticRegularPart, regularizedZetaMul_eq hs]
  simp only [biquadraticHolomorphicFactor, biquadraticLFunction, biquadraticResidue]
  ring

theorem biquadraticRegularPart_at_zero {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1)
    (hz : DirichletCharacter.LFunction χ s = 0) :
    biquadraticRegularPart χ ψ s = -biquadraticResidue χ ψ / (s - 1) := by
  rw [biquadraticRegularPart_eq χ ψ hs]
  simp only [biquadraticLFunction, hz, mul_zero, zero_mul, zero_sub, neg_div]

end Chen
