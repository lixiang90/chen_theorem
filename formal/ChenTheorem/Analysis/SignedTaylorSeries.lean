import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries

namespace Chen

/-- Taylor coefficients in powers of `c - s` rather than `s - c`. -/
noncomputable def backwardTaylorCoeff (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ n * (n.factorial : ℂ)⁻¹ * iteratedDeriv n f c

theorem norm_backwardTaylorCoeff_le {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (Metric.ball c R))
    (hM : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖backwardTaylorCoeff f c n‖ ≤ M * (R⁻¹) ^ n := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf hM
  have h := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hn.le)
  simp only [backwardTaylorCoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    norm_inv, Complex.norm_natCast, one_mul]
  calc
    (n.factorial : ℝ)⁻¹ * ‖iteratedDeriv n f c‖ ≤
        (n.factorial : ℝ)⁻¹ * ((n.factorial : ℝ) * M / R ^ n) := h
    _ = M * (R⁻¹) ^ n := by rw [inv_pow]; field_simp

theorem hasSum_backwardTaylorCoeff {f : ℂ → ℂ} {c z : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c R)) (hz : ‖z‖ < R) :
    HasSum (fun n : ℕ => backwardTaylorCoeff f c n * z ^ n) (f (c - z)) := by
  have hcz : c - z ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm, show c - z - c = -z by ring, norm_neg]
    exact hz
  have he : (fun n : ℕ => backwardTaylorCoeff f c n * z ^ n) =
      (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (c - z - c) ^ n • iteratedDeriv n f c) := by
    funext n
    have hpow : (-z) ^ n = (-1 : ℂ) ^ n * z ^ n := by rw [neg_eq_neg_one_mul, mul_pow]
    simp only [backwardTaylorCoeff, smul_eq_mul, show c - z - c = -z by ring, hpow]
    ring
  rw [he]
  exact Complex.hasSum_taylorSeries_on_ball hf hcz

open scoped ComplexOrder in
theorem backwardTaylorCoeff_nonneg_of_alternating {f : ℂ → ℂ} {c : ℂ}
    (h : ∀ n : ℕ, 0 ≤ (-1 : ℂ) ^ n * iteratedDeriv n f c) (n : ℕ) :
    0 ≤ backwardTaylorCoeff f c n := by
  have hn : 0 ≤ (n.factorial : ℂ)⁻¹ := by positivity
  convert mul_nonneg hn (h n) using 1
  unfold backwardTaylorCoeff
  ring

end Chen
