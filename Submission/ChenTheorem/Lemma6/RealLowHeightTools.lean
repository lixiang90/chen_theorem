import Submission.ChenTheorem.Lemma6.RealZeroSimplicity
import Submission.ChenTheorem.Lemma6.NonrealZeroFreeRegion

set_option autoImplicit true
namespace Chen

theorem conductor_height_log_le_twice_zero_height {q : ℕ} (hq : 2 ≤ q)
    (t : ℝ) (ht : |t| ≤ 1) :
    Real.log ((q : ℝ) * (|t| + 2)) ≤ 2 * Real.log ((q : ℝ) * 2) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  calc
    _ ≤ Real.log (((q : ℝ) * 2) ^ 2) := by
      apply Real.log_le_log (by positivity)
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ q by positivity) (sub_nonneg.mpr ht)]
    _ = _ := by rw [Real.log_pow]; norm_num

theorem principal_shifted_pole_re (x t : ℝ) :
    (((x : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)⁻¹).re =
      x / (x ^ 2 + 4 * t ^ 2) := by
  simp only [Complex.inv_re, Complex.normSq_apply, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.mul_im, mul_zero, sub_zero, add_zero, zero_add, mul_one]
  ring

theorem principal_shifted_pole_mul_le_one_fifth {x t : ℝ} (hx : 0 < x)
    (ht : x ≤ |t|) :
    (((x : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I)⁻¹).re * x ≤ 1 / 5 := by
  rw [principal_shifted_pole_re, div_mul_eq_mul_div]
  have hden : 0 < x ^ 2 + 4 * t ^ 2 := by positivity
  apply (div_le_iff₀ hden).mpr
  have hsq := mul_self_le_mul_self hx.le ht
  rw [← sq, ← sq, sq_abs] at hsq
  nlinarith

theorem norm_principal_shifted_point_sub_one_le {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖(σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I - 1‖ ≤ σ - 1 + 2 * |t| := by
  have he : (σ : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I - 1 =
      ((σ - 1 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by linarith : 0 < σ - 1)]

end Chen
