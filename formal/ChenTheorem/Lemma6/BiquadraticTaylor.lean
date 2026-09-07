import ChenTheorem.Lemma6.BiquadraticRegularPart
import ChenTheorem.Lemma6.ZetaCircleGrowth
import ChenTheorem.Analysis.RegularizedTaylorSeries

namespace Chen

theorem zeta_mul_biquadraticHolomorphicFactor {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (s : ℂ) :
    riemannZeta s * biquadraticHolomorphicFactor χ ψ s = biquadraticLFunction χ ψ s := by
  unfold biquadraticHolomorphicFactor biquadraticLFunction
  ring

theorem backwardTaylorCoeff_biquadraticRegularPart {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) (n : ℕ) :
    backwardTaylorCoeff (biquadraticRegularPart χ ψ) 2 n =
      backwardTaylorCoeff (biquadraticLFunction χ ψ) 2 n - biquadraticResidue χ ψ := by
  have h := backwardTaylorCoeff_regularizedZetaMul
    (differentiable_biquadraticHolomorphicFactor χ ψ hχ hψ hχψ) n
  simpa only [zeta_mul_biquadraticHolomorphicFactor, biquadraticRegularPart, biquadraticResidue] using h

theorem hasSum_biquadraticRegularPart_backwardTaylor {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) (z : ℂ) :
    HasSum (fun n : ℕ => (backwardTaylorCoeff (biquadraticLFunction χ ψ) 2 n -
      biquadraticResidue χ ψ) * z ^ n) (biquadraticRegularPart χ ψ (2 - z)) := by
  have h := hasSum_regularizedZetaMul_backwardTaylor
    (differentiable_biquadraticHolomorphicFactor χ ψ hχ hψ hχψ) z
  simpa only [zeta_mul_biquadraticHolomorphicFactor, biquadraticRegularPart, biquadraticResidue] using h

theorem norm_biquadraticRegularPart_circle_le {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) {B : ℝ} (hB : 0 ≤ B) {s : ℂ}
    (hs : s ∈ Metric.sphere (2 : ℂ) (3 / 2 : ℝ))
    (hf : ‖biquadraticHolomorphicFactor χ ψ s‖ ≤ B) (hr : ‖biquadraticResidue χ ψ‖ ≤ B) :
    ‖biquadraticRegularPart χ ψ s‖ ≤ 12 * B := by
  have hpole := (siegel_circle_geometry hs).2.2
  have hsne : s ≠ 1 := by intro h; norm_num [h] at hpole
  have hprod : ‖biquadraticLFunction χ ψ s‖ ≤ 10 * B := by
    rw [← zeta_mul_biquadraticHolomorphicFactor, norm_mul]
    exact mul_le_mul (norm_riemannZeta_siegel_circle_le hs) hf (norm_nonneg _) (by norm_num)
  have hres : ‖biquadraticResidue χ ψ / (s - 1)‖ ≤ 2 * B := by
    rw [norm_div]
    apply (div_le_iff₀ (by linarith : 0 < ‖s - 1‖)).mpr
    have := mul_le_mul_of_nonneg_left hpole (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB)
    linarith
  rw [biquadraticRegularPart_eq χ ψ hsne]
  exact (norm_sub_le _ _).trans (by linarith)

theorem norm_biquadraticTaylor_sub_residue_le {q : ℕ} [NeZero q]
    (χ ψ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ s ∈ Metric.sphere (2 : ℂ) (3 / 2 : ℝ), ‖biquadraticHolomorphicFactor χ ψ s‖ ≤ B)
    (hr : ‖biquadraticResidue χ ψ‖ ≤ B) (n : ℕ) :
    ‖backwardTaylorCoeff (biquadraticLFunction χ ψ) 2 n - biquadraticResidue χ ψ‖ ≤
      (12 * B) * (2 / 3 : ℝ) ^ n := by
  rw [← backwardTaylorCoeff_biquadraticRegularPart χ ψ hχ hψ hχψ]
  have h := norm_backwardTaylorCoeff_le (R := (3 / 2 : ℝ)) (M := 12 * B) (by norm_num)
    (differentiable_biquadraticRegularPart χ ψ hχ hψ hχψ).diffContOnCl
    (fun s hs => norm_biquadraticRegularPart_circle_le χ ψ hB hs (hf s hs) hr) n
  norm_num only [show (3 / 2 : ℝ)⁻¹ = 2 / 3 by norm_num] at h
  exact h

end Chen
