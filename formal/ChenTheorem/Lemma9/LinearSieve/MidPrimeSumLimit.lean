import ChenTheorem.Lemma9.LinearSieve.UpperPrimeSumLimit

open Set Filter MeasureTheory Finset
open scoped Classical Topology

namespace Chen.LinearSieve

theorem midPrimes_eq_chenFirstPrimes (x : ℕ) : midPrimes x = chenFirstPrimes x := by
  simp only [midPrimes, chenFirstPrimes, one_div]

theorem upperSievePrimeSum_eq_midPrimes (a : ℝ) (x : ℕ) (hx : 1 ≤ x) :
    upperSievePrimeSum a x = ∑ p ∈ midPrimes x, upperSievePrimeWeight a x p / p := by
  rw [midPrimes_eq_chenFirstPrimes x, chenFirstPrimes_eq_Ioc hx]
  simp only [upperSievePrimeSum, div_eq_mul_inv, one_mul]

noncomputable def upperSieveMidPrimeSum (a : ℝ) (x : ℕ) : ℝ :=
  ∑ p ∈ midPrimes x, upperSievePrimeWeight a x p / Nat.totient p

theorem weighted_totient_reciprocal_error (p : ℕ) (hp : p.Prime) (y v : ℝ)
    (hy : 1 < y) (hyp : y ≤ p) (hv : 0 ≤ v) :
    0 ≤ v / Nat.totient p - v / p ∧
      v / Nat.totient p - v / p ≤ (v / p) / (y - 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have heq : v / Nat.totient p - v / p = (v / p) / ((p : ℝ) - 1) := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
    field_simp
    ring
  rw [heq]
  exact ⟨div_nonneg (div_nonneg hv hp0.le) hp1.le,
    div_le_div_of_nonneg_left (div_nonneg hv hp0.le) (by linarith) (by linarith)⟩

theorem upperSieveMidPrimeSum_error_bounds (a : ℝ) (ha : 29 / 60 < a) (x : ℕ) (hx : 2 ≤ x) :
    0 ≤ upperSieveMidPrimeSum a x - upperSievePrimeSum a x ∧
      upperSieveMidPrimeSum a x - upperSievePrimeSum a x ≤
        upperSievePrimeSum a x / ((x : ℝ) ^ (1 / 10 : ℝ) - 1) := by
  have hxR : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hy : 1 < (x : ℝ) ^ (1 / 10 : ℝ) := Real.one_lt_rpow hxR (by norm_num)
  have hpoint (p : ℕ) (hp : p ∈ midPrimes x) :
      0 ≤ upperSievePrimeWeight a x p / Nat.totient p - upperSievePrimeWeight a x p / p ∧
      upperSievePrimeWeight a x p / Nat.totient p - upperSievePrimeWeight a x p / p ≤
        (upperSievePrimeWeight a x p / p) / ((x : ℝ) ^ (1 / 10 : ℝ) - 1) := by
    have hp' := (mem_filter.mp hp).2
    exact weighted_totient_reciprocal_error p hp'.1 _ _ hy hp'.2.1.le
      (upperSievePrimeWeight_bounds a x p ha hxR ⟨hp'.2.1.le, hp'.2.2⟩).1
  rw [upperSievePrimeSum_eq_midPrimes a x (by omega)]
  unfold upperSieveMidPrimeSum
  rw [← sum_sub_distrib]
  constructor
  · exact sum_nonneg (fun p hp => (hpoint p hp).1)
  · rw [sum_div]
    exact sum_le_sum (fun p hp => (hpoint p hp).2)

theorem tendsto_upperSieveMidPrimeSum_error (a : ℝ) (ha : 29 / 60 < a) :
    Tendsto (fun x : ℕ => upperSieveMidPrimeSum a x - upperSievePrimeSum a x) atTop (𝓝 0) := by
  have hsum := (tendsto_upperSievePrimeSum a ha).comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun x : ℕ => (x : ℝ) ^ (1 / 10 : ℝ) - 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-1)
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp tendsto_natCast_atTop_atTop)
  have hlim := hsum.div_atTop hpow
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
    exact (upperSieveMidPrimeSum_error_bounds a ha x hx).1
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
    exact (upperSieveMidPrimeSum_error_bounds a ha x hx).2

theorem tendsto_upperSieveMidPrimeSum (a : ℝ) (ha : 29 / 60 < a) :
    Tendsto (upperSieveMidPrimeSum a) atTop
      (𝓝 (∫ α : ℝ in (1 / 10)..(1 / 3), upperLinearSieveFunction (10 * a - 10 * α) / α)) := by
  have h := (tendsto_upperSieveMidPrimeSum_error a ha).add
    ((tendsto_upperSievePrimeSum a ha).comp tendsto_natCast_atTop_atTop)
  simpa only [sub_add_cancel, zero_add, Function.comp_def] using h

end Chen.LinearSieve
