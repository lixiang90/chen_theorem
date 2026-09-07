import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.TaylorSeries

set_option autoImplicit true

namespace Chen

theorem norm_tsum_nat_add_le_geometric {a : ℕ → ℂ} {M r : ℝ}
    (hr : 0 ≤ r) (hr' : r < 1) (ha : ∀ n, ‖a n‖ ≤ M * r ^ n) (k : ℕ) :
    ‖∑' n : ℕ, a (n + k)‖ ≤ M * r ^ k / (1 - r) := by
  have hg := (hasSum_geometric_of_lt_one hr hr').mul_left (M * r ^ k)
  have hb (n : ℕ) : ‖a (n + k)‖ ≤ M * r ^ k * r ^ n := by
    calc
      ‖a (n + k)‖ ≤ M * r ^ (n + k) := ha _
      _ = M * r ^ k * r ^ n := by rw [pow_add]; ring
  simpa only [div_eq_mul_inv] using tsum_of_norm_bounded hg hb

theorem powerSeries_tail_norm_le {a : ℕ → ℂ} {M r x : ℝ}
    (hr : 0 ≤ r) (hx : 0 ≤ x) (hrx : r * x < 1)
    (ha : ∀ n, ‖a n‖ ≤ M * r ^ n) (k : ℕ) :
    ‖∑' n : ℕ, a (n + k) * (x : ℂ) ^ (n + k)‖ ≤
      M * (r * x) ^ k / (1 - r * x) := by
  refine norm_tsum_nat_add_le_geometric (a := fun n => a n * (x : ℂ) ^ n)
    (mul_nonneg hr hx) hrx ?_ k
  intro n
  rw [norm_mul, norm_pow, Complex.norm_of_nonneg hx]
  calc
    ‖a n‖ * x ^ n ≤ (M * r ^ n) * x ^ n :=
      mul_le_mul_of_nonneg_right (ha n) (pow_nonneg hx n)
    _ = M * (r * x) ^ n := by rw [mul_pow]; ring

theorem powerSeries_summable_of_geometric_bound {a : ℕ → ℂ} {M r x : ℝ}
    (hr : 0 ≤ r) (hx : 0 ≤ x) (hrx : r * x < 1)
    (ha : ∀ n, ‖a n‖ ≤ M * r ^ n) :
    Summable (fun n : ℕ => a n * (x : ℂ) ^ n) := by
  apply ((summable_geometric_of_lt_one (mul_nonneg hr hx) hrx).mul_left M).of_norm_bounded
  intro n
  rw [norm_mul, norm_pow, Complex.norm_of_nonneg hx]
  calc
    ‖a n‖ * x ^ n ≤ (M * r ^ n) * x ^ n :=
      mul_le_mul_of_nonneg_right (ha n) (pow_nonneg hx n)
    _ = M * (r * x) ^ n := by rw [mul_pow]; ring

/-- Truncating a Taylor series with nonnegative uncorrected coefficients.
The coefficients `b n - ρ` are those of a function after removing its simple pole. -/
theorem siegelTaylor_lower_bound {b : ℕ → ℂ} {F : ℂ} {ρ M r x : ℝ}
    (hb : ∀ n, 0 ≤ (b n).re) (hb0 : 1 ≤ (b 0).re)
    (hx : 1 < x) (hr : 0 ≤ r) (hrx : r * x < 1)
    (hbound : ∀ n, ‖b n - (ρ : ℂ)‖ ≤ M * r ^ n)
    (hsum : HasSum (fun n : ℕ => (b n - (ρ : ℂ)) * (x : ℂ) ^ n)
      (F + ((ρ / (x - 1) : ℝ) : ℂ)))
    (k : ℕ) (hk : 1 ≤ k) :
    1 - ρ * x ^ k / (x - 1) - M * (r * x) ^ k / (1 - r * x) ≤ F.re := by
  have hx0 : 0 ≤ x := by linarith
  have hpartial : 1 ≤ ∑ n ∈ Finset.range k, (b n).re * x ^ n := by
    calc
      1 ≤ (b 0).re * x ^ 0 := by simpa using hb0
      _ ≤ ∑ n ∈ Finset.range k, (b n).re * x ^ n :=
        Finset.single_le_sum (fun n _ => mul_nonneg (hb n) (pow_nonneg hx0 n))
          (Finset.mem_range.mpr (by omega))
  have htail := powerSeries_tail_norm_le hr hx0 hrx hbound k
  have htailre := (Complex.abs_re_le_norm
    (∑' n : ℕ, (b (n + k) - (ρ : ℂ)) * (x : ℂ) ^ (n + k))).trans htail
  have he := hsum.summable.sum_add_tsum_nat_add k
  rw [hsum.tsum_eq] at he
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re, Complex.re_sum, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_im, mul_zero, sub_zero] at hre
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    geom_sum_eq (ne_of_gt hx)] at hre
  have ht := (abs_le.mp htailre).1
  simp only [← Complex.ofReal_pow, sub_mul] at ht
  have hid : ρ * (x ^ k - 1) / (x - 1) + ρ / (x - 1) = ρ * x ^ k / (x - 1) := by ring
  simp only [mul_div_assoc] at hid ht ⊢
  linarith

end Chen
