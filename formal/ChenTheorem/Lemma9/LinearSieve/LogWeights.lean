import ChenTheorem.Lemma9.LinearSieve.WeightedPrimeSieve

open Finset
open scoped Classical

namespace Chen.LinearSieve

/-- Removing logarithmic weights for a lower bound on a finite count. -/
theorem sum_log_le_log_mul_card (S : Finset ℕ) (x : ℕ)
    (hpos : ∀ p ∈ S, 0 < p) (hx : ∀ p ∈ S, p ≤ x) :
    (∑ p ∈ S, Real.log p) ≤ Real.log x * S.card := by
  calc
    _ ≤ ∑ _p ∈ S, Real.log x := sum_le_sum (fun p hp =>
      Real.log_le_log (by exact_mod_cast hpos p hp) (by exact_mod_cast hx p hp))
    _ = _ := by simp [mul_comm]

/-- An upper count bound uses a lower logarithmic cutoff. Only elements
below the cutoff incur an unweighted loss. -/
theorem log_mul_card_le_sum_log_add_small (S : Finset ℕ) (T : ℝ)
    (hpos : ∀ p ∈ S, 0 < p) (hT : 0 < T) :
    T.log * S.card ≤ (∑ p ∈ S, Real.log p) +
      T.log * (S.filter (fun p : ℕ => (p : ℝ) < T)).card := by
  calc
    _ = ∑ _p ∈ S, T.log := by simp [mul_comm]
    _ ≤ ∑ p ∈ S, (Real.log p + if (p : ℝ) < T then T.log else 0) := by
      apply sum_le_sum
      intro p hp
      split_ifs with h
      · have hlog : 0 ≤ Real.log (p : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hpos p hp)
        linarith
      · simp only [add_zero]
        exact Real.log_le_log hT (le_of_not_gt h)
    _ = _ := by rw [sum_add_distrib, ← sum_filter]; simp [mul_comm]

theorem card_le_sum_log_div_log_add_small (S : Finset ℕ) (T : ℝ)
    (hpos : ∀ p ∈ S, 0 < p) (hT : 1 < T) :
    (S.card : ℝ) ≤ (∑ p ∈ S, Real.log p) / T.log +
      (S.filter (fun p : ℕ => (p : ℝ) < T)).card := by
  have hlog := Real.log_pos hT
  have h := log_mul_card_le_sum_log_add_small S T hpos (by linarith)
  calc
    _ ≤ ((∑ p ∈ S, Real.log p) +
        T.log * (S.filter (fun p : ℕ => (p : ℝ) < T)).card) / T.log :=
      (le_div_iff₀ hlog).mpr (by simpa only [mul_comm] using h)
    _ = _ := by rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hlog)]

/-- The primes surviving a finite difference sieve. -/
noncomputable def primeDifferenceSiftedPrimes (x : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun p => p.Prime ∧ (∏ r ∈ P, r).Coprime (x - p))

/-- Surviving primes with one extra divisibility condition. -/
noncomputable def primeDifferenceSiftedPrimesAt (x k : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (primeDifferenceSiftedPrimes x P).filter (fun p => k ∣ x - p)

theorem primeDifferenceSiftedSum_eq_sum_log (x : ℕ) (P : Finset ℕ) :
    primeDifferenceSiftedSum x P = ∑ p ∈ primeDifferenceSiftedPrimes x P, Real.log p := by
  simp only [primeDifferenceSiftedSum, primeDifferenceSiftedPrimes, sum_filter]

theorem primeDifferenceSiftedSumAt_eq_sum_log (x k : ℕ) (P : Finset ℕ) :
    primeDifferenceSiftedSumAt x k P =
      ∑ p ∈ primeDifferenceSiftedPrimesAt x k P, Real.log p := by
  unfold primeDifferenceSiftedSumAt primeDifferenceSiftedPrimesAt primeDifferenceSiftedPrimes
  simp only [sum_filter]
  apply sum_congr rfl
  intro p _
  split_ifs <;> simp_all

/-- Lower conversion for the main sieve term. -/
theorem primeDifferenceSiftedSum_div_log_le_card (x : ℕ) (hx : 1 < x) (P : Finset ℕ) :
    primeDifferenceSiftedSum x P / Real.log x ≤
      (primeDifferenceSiftedPrimes x P).card := by
  apply (div_le_iff₀ (Real.log_pos (by exact_mod_cast hx))).mpr
  rw [primeDifferenceSiftedSum_eq_sum_log]
  simpa only [mul_comm] using sum_log_le_log_mul_card (primeDifferenceSiftedPrimes x P) x
    (fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).1)
    (fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).2)

/-- Upper conversion for the middle-prime correction; the small-prime
loss will be summed before estimation to exploit bounded multiplicity. -/
theorem primeDifferenceSiftedPrimesAt_card_le (x k : ℕ) (P : Finset ℕ)
    (T : ℝ) (hT : 1 < T) :
    ((primeDifferenceSiftedPrimesAt x k P).card : ℝ) ≤
      primeDifferenceSiftedSumAt x k P / T.log +
        ((primeDifferenceSiftedPrimesAt x k P).filter (fun p : ℕ => (p : ℝ) < T)).card := by
  rw [primeDifferenceSiftedSumAt_eq_sum_log]
  exact card_le_sum_log_div_log_add_small _ T
    (fun p hp => (mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1) hT

end Chen.LinearSieve
