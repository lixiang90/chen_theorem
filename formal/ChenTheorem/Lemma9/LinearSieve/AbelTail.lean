import Mathlib.NumberTheory.AbelSummation

open Finset MeasureTheory

namespace Chen.LinearSieve

/-- Tail of a finite coefficient sum, written as a difference of prefix
sums so that it is defined for every real argument. -/
noncomputable def coefficientTail (c : ℕ → ℝ) (b t : ℝ) : ℝ :=
  (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - ∑ k ∈ Icc 0 ⌊t⌋₊, c k

theorem integrableOn_deriv_mul_coefficientTail (c : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a)
    (f : ℝ → ℝ) (hf : IntegrableOn (deriv f) (Set.Icc a b)) :
    IntegrableOn (fun t => deriv f t * coefficientTail c b t) (Set.Icc a b) := by
  have hsum := integrableOn_mul_sum_Icc c (m := 0) ha hf
  apply ((hf.mul_const (∑ k ∈ Icc 0 ⌊b⌋₊, c k)).sub hsum).congr
  exact Filter.Eventually.of_forall (fun t => (mul_sub _ _ _).symm)

/-- Abel summation in tail form. This is the useful orientation when
the cumulative tail is bounded above and the test function increases. -/
theorem sum_mul_eq_coefficientTail_integral (c : ℕ → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hfd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hfi : IntegrableOn (deriv f) (Set.Icc a b)) :
    (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k) =
      f a * coefficientTail c b a +
        ∫ t in Set.Ioc a b, deriv f t * coefficientTail c b t := by
  have habel := sum_mul_eq_sub_sub_integral_mul c ha hab hfd hfi
  have hsum := integrableOn_mul_sum_Icc c (m := 0) ha hfi
  have hFTC : (∫ t in Set.Ioc a b, deriv f t) = f b - f a := by
    rw [← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_deriv_eq_sub
    · simpa only [Set.uIcc_of_le hab] using hfd
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hfi
  have hint : (∫ t in Set.Ioc a b, deriv f t * coefficientTail c b t) =
      (f b - f a) * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) -
        ∫ t in Set.Ioc a b, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
    simp only [coefficientTail, mul_sub]
    rw [integral_sub (IntegrableOn.mono_set (hfi.mul_const _) Set.Ioc_subset_Icc_self)
      (hsum.mono_set Set.Ioc_subset_Icc_self), integral_mul_const, hFTC]
  rw [hint, coefficientTail, habel]
  ring

/-- A cumulative upper bound controls every increasing differentiable
test function. Integrability of the proposed majorant is explicit. -/
theorem sum_mul_le_coefficientTail_majorant (c : ℕ → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (f M : ℝ → ℝ)
    (hfd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hfi : IntegrableOn (deriv f) (Set.Icc a b))
    (hfa : 0 ≤ f a) (hderiv : ∀ t ∈ Set.Icc a b, 0 ≤ deriv f t)
    (hM : ∀ t ∈ Set.Icc a b, coefficientTail c b t ≤ M t)
    (hMi : IntegrableOn (fun t => deriv f t * M t) (Set.Icc a b)) :
    (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k) ≤
      f a * M a + ∫ t in Set.Ioc a b, deriv f t * M t := by
  rw [sum_mul_eq_coefficientTail_integral c a b ha hab f hfd hfi]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hM a ⟨le_rfl, hab⟩) hfa
  · apply setIntegral_mono_on
      ((integrableOn_deriv_mul_coefficientTail c a b ha f hfi).mono_set
        Set.Ioc_subset_Icc_self)
      (hMi.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc
    intro t ht
    exact mul_le_mul_of_nonneg_left (hM t ⟨ht.1.le, ht.2⟩)
      (hderiv t ⟨ht.1.le, ht.2⟩)

end Chen.LinearSieve
