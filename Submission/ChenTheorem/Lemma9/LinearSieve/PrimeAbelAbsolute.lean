import Submission.ChenTheorem.Lemma8.PrimeReciprocal

set_option autoImplicit true
open Set MeasureTheory
open scoped Classical

namespace Chen.LinearSieve

/-- Two-sided Abel error for a nonnegative increasing weight. -/
theorem abs_primeReciprocal_abel_error_le
    {a b ε : ℝ} (ha : 1 < a) (hab : a ≤ b) (hε : 0 ≤ ε) (f : ℝ → ℝ)
    (hf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hi : IntegrableOn (deriv f) (Icc a b))
    (hE : ∀ t ∈ Icc a b, |primeReciprocalError t| ≤ ε)
    (hfa : 0 ≤ f a) (hfb : 0 ≤ f b)
    (hd : ∀ t ∈ Ioc a b, 0 ≤ deriv f t) :
    |(∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with p.Prime, f p * (p : ℝ)⁻¹) -
      ∫ t in Ioc a b, f t / (t * Real.log t)| ≤ 2 * ε * f b := by
  have hprod := integrableOn_deriv_mul_primeReciprocalError ha f hi
  have hFTC : (∫ t in Ioc a b, deriv f t) = f b - f a := by
    rw [← intervalIntegral.integral_of_le hab]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => (hf t (by simpa only [uIcc_of_le hab] using ht)).hasDerivAt)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hi)
  have hupper := abel_error_le_of_nonneg_deriv hab hε hE hfa hfb hd
    (hi.mono_set Ioc_subset_Icc_self) hprod hFTC
  have hnegE : ∀ t ∈ Icc a b, |(-primeReciprocalError t)| ≤ ε := by
    intro t ht
    simpa only [abs_neg] using hE t ht
  have hnegint : IntegrableOn (fun t => deriv f t * (-primeReciprocalError t)) (Ioc a b) := by
    simpa only [Pi.neg_def, mul_neg] using hprod.neg
  have hlower := abel_error_le_of_nonneg_deriv hab hε hnegE hfa hfb hd
    (hi.mono_set Ioc_subset_Icc_self) hnegint hFTC
  simp only [mul_neg, integral_neg] at hlower
  rw [primeReciprocal_abel_decomposition_auto ha hab f hf hi]
  apply abs_le.mpr
  constructor <;> linarith

end Chen.LinearSieve
