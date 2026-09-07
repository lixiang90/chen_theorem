import ChenTheorem.Lemma6.BiquadraticTaylorBound
import ChenTheorem.Lemma6.RealCharacterConjugation
import ChenTheorem.Analysis.SiegelTaylorInequality

open ComplexConjugate

namespace Chen

theorem biquadraticResidue_eq_re {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    (hχsq : χ ^ 2 = 1) (hψsq : ψ ^ 2 = 1) :
    ((biquadraticResidue χ ψ).re : ℂ) = biquadraticResidue χ ψ := by
  apply Complex.conj_eq_iff_re.mp
  have hprodsq : (χ * ψ) ^ 2 = 1 := by rw [mul_pow, hχsq, hψsq, one_mul]
  simp only [biquadraticResidue, biquadraticHolomorphicFactor, map_mul,
    conj_LFunction_of_nonprincipal_real_character χ hχ hχsq,
    conj_LFunction_of_nonprincipal_real_character ψ hψ hψsq,
    conj_LFunction_of_nonprincipal_real_character (χ * ψ) hχψ hprodsq, map_one]

/-- The quantitative finite Taylor inequality for the actual biquadratic product.
It holds before any truncation index is chosen. -/
theorem biquadraticLFunction_taylor_lower_bound {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    (hχsq : χ ^ 2 = 1) (hψsq : ψ ^ 2 = 1) (β : ℝ)
    (hβ : 7 / 8 < β) (hβ' : β < 1) (k : ℕ) (hk : 1 ≤ k) :
    1 - (biquadraticResidue χ ψ).re * (2 - β) ^ k / (1 - β) -
      (12 * (42 * (q : ℝ) ^ 3) ^ 3) * ((2 / 3 : ℝ) * (2 - β)) ^ k /
        (1 - (2 / 3 : ℝ) * (2 - β)) ≤ (biquadraticLFunction χ ψ (β : ℂ)).re := by
  have hρ := biquadraticResidue_eq_re χ ψ hχ hψ hχψ hχsq hψsq
  have hb (n : ℕ) : 0 ≤ (backwardTaylorCoeff (biquadraticLFunction χ ψ) 2 n).re :=
    (Complex.le_def.mp (backwardTaylorCoeff_biquadratic_nonneg χ ψ hχsq hψsq 2 (by norm_num) n)).1
  have hb0 : 1 ≤ (backwardTaylorCoeff (biquadraticLFunction χ ψ) 2 0).re := by
    simpa [backwardTaylorCoeff] using
      (Complex.le_def.mp (biquadraticLFunction_real_ge_one χ ψ hχsq hψsq 2 (by norm_num))).1
  have hbound (n : ℕ) := norm_biquadraticTaylor_sub_residue_le_level χ ψ hχ hψ hχψ n
  have hsum := hasSum_biquadraticRegularPart_backwardTaylor χ ψ hχ hψ hχψ ((2 - β : ℝ) : ℂ)
  have heval : (2 : ℂ) - ((2 - β : ℝ) : ℂ) = (β : ℂ) := by push_cast; ring
  rw [heval, biquadraticRegularPart_eq χ ψ (by exact_mod_cast ne_of_lt hβ')] at hsum
  have hvalue : biquadraticLFunction χ ψ (β : ℂ) - biquadraticResidue χ ψ / ((β : ℂ) - 1) =
      biquadraticLFunction χ ψ (β : ℂ) + (((biquadraticResidue χ ψ).re / ((2 - β) - 1) : ℝ) : ℂ) := by
    rw [← hρ]
    simp only [Complex.ofReal_re]
    push_cast
    have he : (2 : ℂ) - β - 1 = -((β : ℂ) - 1) := by ring
    rw [he, div_neg]
    ring
  rw [hvalue, ← hρ] at hsum
  have h := siegelTaylor_lower_bound hb hb0 (by linarith : (1 : ℝ) < 2 - β)
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (by linarith : (2 / 3 : ℝ) * (2 - β) < 1)
    (fun n => by rw [hρ]; exact hbound n) hsum k hk
  simpa only [show (2 - β) - 1 = 1 - β by ring] using h

end Chen
