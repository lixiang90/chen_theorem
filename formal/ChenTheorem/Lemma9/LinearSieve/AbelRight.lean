/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot

Adapted from Mathlib.NumberTheory.AbelSummation: replace two-sided derivatives
by integrable right derivatives to allow the junctions of the Rosser terms.
-/
import ChenTheorem.Lemma9.LinearSieve.AbelTail

open Finset MeasureTheory

namespace Chen.LinearSieve
namespace AbelRight

open intervalIntegral IntervalIntegrable

variable (c : ℕ → ℝ) {f g : ℝ → ℝ} {a b : ℝ}
private theorem sumlocc {m : ℕ} (n : ℕ) :
    ∀ᵐ t, t ∈ Set.Icc (n : ℝ) (n + 1) → ∑ k ∈ Icc m ⌊t⌋₊, c k = ∑ k ∈ Icc m n, c k := by
  filter_upwards [Ico_ae_eq_Icc] with t h ht
  rw [Nat.floor_eq_on_Ico _ _ (h.mpr ht)]

open scoped Interval in
private theorem integralmulsum (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : ∀ t ∈ Set.Ioo a b, HasDerivWithinAt f (g t) (Set.Ioi t) t)
    (hf_int : IntegrableOn (g) (Set.Icc a b)) (t₁ t₂ : ℝ) (n : ℕ) (h : t₁ ≤ t₂)
    (h₁ : n ≤ t₁) (h₂ : t₂ ≤ n + 1) (h₃ : a ≤ t₁) (h₄ : t₂ ≤ b) :
    ∫ t in t₁..t₂, g t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k =
      (f t₂ - f t₁) * ∑ k ∈ Icc 0 n, c k := by
  have h_inc₁ : Ι t₁ t₂ ⊆ Set.Icc n (n + 1) :=
    Set.uIoc_of_le h ▸ Set.Ioc_subset_Icc_self.trans <| Set.Icc_subset_Icc h₁ h₂
  have h_inc₂ : Set.uIcc t₁ t₂ ⊆ Set.Icc a b := Set.uIcc_of_le h ▸ Set.Icc_subset_Icc h₃ h₄
  rw [← integral_eq_sub_of_hasDeriv_right_of_le h
      (hf_cont.mono (Set.Icc_subset_Icc h₃ h₄))
      (fun t ht ↦ hf_diff t ⟨lt_of_le_of_lt h₃ ht.1, lt_of_lt_of_le ht.2 h₄⟩),
      ← intervalIntegral.integral_mul_const]
  · refine integral_congr_ae ?_
    filter_upwards [sumlocc c n] with t h h'
    rw [h (h_inc₁ h')]
  · refine (intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr (hf_int.mono_set ?_)
    rwa [← Set.uIcc_of_le h]

private theorem ineqofmemIco {k : ℕ} (hk : k ∈ Set.Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b := by
  constructor
  · have := (Set.mem_Ico.mp hk).1
    exact le_of_lt <| (Nat.floor_lt' (by lia)).mp this
  · rw [← Nat.cast_add_one, ← Nat.le_floor_iff' (Nat.succ_ne_zero k)]
    exact (Set.mem_Ico.mp hk).2

private theorem ineqofmemIco' {k : ℕ} (hk : k ∈ Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b :=
  ineqofmemIco (by rwa [← Finset.coe_Ico])

/-- Abel's summation formula. -/
theorem sum_mul_eq_sub_sub_integral_of_hasDeriv_right (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : ∀ t ∈ Set.Ioo a b, HasDerivWithinAt f (g t) (Set.Ioi t) t)
    (hf_int : IntegrableOn (g) (Set.Icc a b)) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k =
      f b * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) - f a * (∑ k ∈ Icc 0 ⌊a⌋₊, c k) -
        ∫ t in Set.Ioc a b, g t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  rw [← integral_of_le hab]
  have aux1 : ⌊a⌋₊ ≤ a := Nat.floor_le ha
  have aux2 : b ≤ ⌊b⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  -- We consider two cases depending on whether the sum is empty or not
  obtain hb | hb := eq_or_lt_of_le (Nat.floor_le_floor hab)
  · rw [hb, Ioc_eq_empty_of_le le_rfl, sum_empty, ← sub_mul,
      integralmulsum c hf_cont hf_diff hf_int _ _ ⌊b⌋₊ hab (hb ▸ aux1) aux2 le_rfl le_rfl, sub_self]
  have aux3 : a ≤ ⌊a⌋₊ + 1 := (Nat.lt_floor_add_one _).le
  have aux4 : ⌊a⌋₊ + 1 ≤ b := by rwa [← Nat.cast_add_one, ← Nat.le_floor_iff (ha.trans hab)]
  have aux5 : ⌊b⌋₊ ≤ b := Nat.floor_le (ha.trans hab)
  have aux6 : a ≤ ⌊b⌋₊ := Nat.floor_lt ha |>.mp hb |>.le
  simp_rw [← smul_eq_mul, sum_Ioc_by_parts (fun k ↦ f k) _ hb, range_eq_Ico,
    Ico_add_one_right_eq_Icc, smul_eq_mul]
  have : ∑ k ∈ Ioc ⌊a⌋₊ (⌊b⌋₊ - 1), (f ↑(k + 1) - f k) * ∑ n ∈ Icc 0 k, c n =
        ∑ k ∈ Ico (⌊a⌋₊ + 1) ⌊b⌋₊, ∫ t in k..↑(k + 1), g t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n := by
    rw [← Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel (by lia), Eq.comm]
    exact sum_congr rfl fun k hk ↦ (integralmulsum c hf_cont hf_diff hf_int _ _ _ (mod_cast k.le_succ)
      le_rfl (mod_cast le_rfl) (ineqofmemIco' hk).1 <| mod_cast (ineqofmemIco' hk).2)
  rw [this, sum_integral_adjacent_intervals_Ico hb, Nat.cast_add, Nat.cast_one,
    ← integral_interval_sub_left (a := a) (c := ⌊a⌋₊ + 1),
    ← integral_add_adjacent_intervals (b := ⌊b⌋₊) (c := b),
    integralmulsum c hf_cont hf_diff hf_int _ _ _ aux3 aux1 le_rfl le_rfl aux4,
    integralmulsum c hf_cont hf_diff hf_int _ _ _ aux5 le_rfl aux2 aux6 le_rfl]
  · ring
  -- now deal with the integrability side goals
  -- (Note we have 5 goals, but the 1st and 3rd are identical. TODO: find a non-hacky way of dealing
  -- with both at once.)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux6]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux5)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux5]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_left aux6)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux6]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux5)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le aux3]
    exact (integrableOn_mul_sum_Icc c ha hf_int).mono_set (Set.Icc_subset_Icc_right aux4)
  · exact fun k hk ↦ (intervalIntegrable_iff_integrableOn_Icc_of_le (mod_cast k.le_succ)).mpr
      <| (integrableOn_mul_sum_Icc c ha hf_int).mono_set
        <| (Set.Icc_subset_Icc_iff (mod_cast k.le_succ)).mpr <| mod_cast (ineqofmemIco hk)


end AbelRight
theorem integrableOn_mul_coefficientTail (c : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a)
    (g : ℝ → ℝ) (hf : IntegrableOn (g) (Set.Icc a b)) :
    IntegrableOn (fun t => g t * coefficientTail c b t) (Set.Icc a b) := by
  have hsum := integrableOn_mul_sum_Icc c (m := 0) ha hf
  apply ((hf.mul_const (∑ k ∈ Icc 0 ⌊b⌋₊, c k)).sub hsum).congr
  exact Filter.Eventually.of_forall (fun t => (mul_sub _ _ _).symm)

/-- Abel summation in tail form. This is the useful orientation when
the cumulative tail is bounded above and the test function increases. -/
theorem sum_mul_eq_coefficientTail_integral_of_hasDeriv_right (c : ℕ → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (f g : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : ∀ t ∈ Set.Ioo a b, HasDerivWithinAt f (g t) (Set.Ioi t) t)
    (hfi : IntegrableOn (g) (Set.Icc a b)) :
    (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k) =
      f a * coefficientTail c b a +
        ∫ t in Set.Ioc a b, g t * coefficientTail c b t := by
  have habel := AbelRight.sum_mul_eq_sub_sub_integral_of_hasDeriv_right c ha hab hfc hfd hfi
  have hsum := integrableOn_mul_sum_Icc c (m := 0) ha hfi
  have hFTC : (∫ t in Set.Ioc a b, g t) = f b - f a := by
    rw [← intervalIntegral.integral_of_le hab]
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hfc hfd
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hfi)
  have hint : (∫ t in Set.Ioc a b, g t * coefficientTail c b t) =
      (f b - f a) * (∑ k ∈ Icc 0 ⌊b⌋₊, c k) -
        ∫ t in Set.Ioc a b, g t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
    simp only [coefficientTail, mul_sub]
    rw [integral_sub (IntegrableOn.mono_set (hfi.mul_const _) Set.Ioc_subset_Icc_self)
      (hsum.mono_set Set.Ioc_subset_Icc_self), integral_mul_const, hFTC]
  rw [hint, coefficientTail, habel]
  ring

/-- A cumulative upper bound controls every increasing differentiable
test function. Integrability of the proposed majorant is explicit. -/
theorem sum_mul_le_coefficientTail_majorant_of_hasDeriv_right (c : ℕ → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (f g M : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hfd : ∀ t ∈ Set.Ioo a b, HasDerivWithinAt f (g t) (Set.Ioi t) t)
    (hfi : IntegrableOn (g) (Set.Icc a b))
    (hfa : 0 ≤ f a) (hderiv : ∀ t ∈ Set.Icc a b, 0 ≤ g t)
    (hM : ∀ t ∈ Set.Icc a b, coefficientTail c b t ≤ M t)
    (hMi : IntegrableOn (fun t => g t * M t) (Set.Icc a b)) :
    (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k) ≤
      f a * M a + ∫ t in Set.Ioc a b, g t * M t := by
  rw [sum_mul_eq_coefficientTail_integral_of_hasDeriv_right c a b ha hab f g hfc hfd hfi]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hM a ⟨le_rfl, hab⟩) hfa
  · apply setIntegral_mono_on
      ((integrableOn_mul_coefficientTail c a b ha g hfi).mono_set
        Set.Ioc_subset_Icc_self)
      (hMi.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc
    intro t ht
    exact mul_le_mul_of_nonneg_left (hM t ⟨ht.1.le, ht.2⟩)
      (hderiv t ⟨ht.1.le, ht.2⟩)



end Chen.LinearSieve


