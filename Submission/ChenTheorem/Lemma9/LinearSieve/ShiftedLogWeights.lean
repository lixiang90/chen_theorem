import Submission.ChenTheorem.Lemma9.LinearSieve.ShiftedWeightedPrimeSieve
import Submission.ChenTheorem.Lemma9.LinearSieve.SmallPrimeLoss

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

noncomputable def primeShiftSiftedPrimes (h x : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (Icc 1 x).filter (fun p => p.Prime ∧ (∏ r ∈ P, r).Coprime (p + h))

noncomputable def primeShiftSiftedPrimesAt (h x k : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (primeShiftSiftedPrimes h x P).filter (fun p => k ∣ p + h)

theorem primeShiftSiftedSum_eq_sum_log (h x : ℕ) (P : Finset ℕ) :
    primeShiftSiftedSum h x P = ∑ p ∈ primeShiftSiftedPrimes h x P, Real.log p := by
  simp only [primeShiftSiftedSum, primeShiftSiftedPrimes, sum_filter]

theorem primeShiftSiftedSumAt_eq_sum_log (h x k : ℕ) (P : Finset ℕ) :
    primeShiftSiftedSumAt h x k P =
      ∑ p ∈ primeShiftSiftedPrimesAt h x k P, Real.log p := by
  unfold primeShiftSiftedSumAt primeShiftSiftedPrimesAt primeShiftSiftedPrimes
  simp only [sum_filter]
  apply sum_congr rfl
  intro p _
  split_ifs <;> simp_all

theorem primeShiftSiftedSum_div_log_le_card (h x : ℕ) (hx : 1 < x) (P : Finset ℕ) :
    primeShiftSiftedSum h x P / Real.log x ≤ (primeShiftSiftedPrimes h x P).card := by
  apply (div_le_iff₀ (Real.log_pos (by exact_mod_cast hx))).mpr
  rw [primeShiftSiftedSum_eq_sum_log]
  simpa only [mul_comm] using sum_log_le_log_mul_card (primeShiftSiftedPrimes h x P) x
    (fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).1)
    (fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).2)

theorem primeShiftSiftedPrimesAt_card_le (h x k : ℕ) (P : Finset ℕ)
    (T : ℝ) (hT : 1 < T) :
    ((primeShiftSiftedPrimesAt h x k P).card : ℝ) ≤
      primeShiftSiftedSumAt h x k P / T.log +
        ((primeShiftSiftedPrimesAt h x k P).filter (fun p : ℕ => (p : ℝ) < T)).card := by
  rw [primeShiftSiftedSumAt_eq_sum_log]
  exact card_le_sum_log_div_log_add_small _ T
    (fun p hp => (mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1) hT

/-- For primes below `T`, the condition `T+h ≤ x` keeps `p+h` in the
range of the ten-large-prime-divisors bound. This avoids multiplying the
small-prime loss by the number of middle primes. -/
theorem sum_primeShift_small_card_le (h x : ℕ) (hx : 1 < x)
    (P K : Finset ℕ) (hK : ∀ k ∈ K, Nat.Prime k)
    (hlarge : ∀ k ∈ K, (x : ℝ) ^ ((1 : ℝ) / 10) < k)
    (T : ℝ) (hTx : T + h ≤ x) :
    (∑ k ∈ K, ((primeShiftSiftedPrimesAt h x k P).filter
      (fun p : ℕ => (p : ℝ) < T)).card) ≤ 10 * ⌈T⌉₊ := by
  let S := (primeShiftSiftedPrimes h x P).filter (fun p : ℕ => (p : ℝ) < T)
  have heq : (∑ k ∈ K, ((primeShiftSiftedPrimesAt h x k P).filter
      (fun p : ℕ => (p : ℝ) < T)).card) =
      ∑ p ∈ S, (K.filter (fun k => k ∣ p + h)).card := by
    unfold primeShiftSiftedPrimesAt
    have hfilter (k : ℕ) : ((primeShiftSiftedPrimes h x P).filter (fun p => k ∣ p + h)).filter
        (fun p : ℕ => (p : ℝ) < T) = S.filter (fun p => k ∣ p + h) := by
      ext p
      simp only [S, mem_filter]
      tauto
    simp_rw [hfilter]
    simp only [card_eq_sum_ones, sum_filter]
    exact sum_comm
  rw [heq]
  have hmult (p : ℕ) (hp : p ∈ S) : (K.filter (fun k => k ∣ p + h)).card ≤ 10 := by
    have hpp : p.Prime := (mem_filter.mp (mem_filter.mp hp).1).2.1
    have hpT : (p : ℝ) < T := (mem_filter.mp hp).2
    have hpx : p + h ≤ x := by
      have hc : (p : ℝ) + h ≤ x := by linarith
      exact_mod_cast hc
    exact card_large_prime_divisors_le_ten _ x (p + h) hx (by have := hpp.pos; omega) hpx
      (fun k hk => hK k (mem_filter.mp hk).1)
      (fun k hk => (mem_filter.mp hk).2)
      (fun k hk => hlarge k (mem_filter.mp hk).1)
  have hcard : S.card ≤ ⌈T⌉₊ := by
    apply (card_le_card (show S ⊆ range ⌈T⌉₊ from ?_)).trans_eq (card_range _)
    intro p hp
    exact mem_range.mpr (Nat.lt_ceil.mpr (mem_filter.mp hp).2)
  calc
    _ ≤ ∑ _p ∈ S, 10 := sum_le_sum hmult
    _ = 10 * S.card := by simp [mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left 10 hcard

noncomputable def primeShiftWeightedCount (h x : ℕ) (P K : Finset ℕ) : ℝ :=
  (primeShiftSiftedPrimes h x P).card -
    (1 / 2) * ∑ k ∈ K, ((primeShiftSiftedPrimesAt h x k P).card : ℝ)

theorem primeShift_count_lower_of_log_bounds (h x : ℕ) (hx : 1 < x)
    (P K : Finset ℕ) (hK : ∀ k ∈ K, Nat.Prime k)
    (hlarge : ∀ k ∈ K, (x : ℝ) ^ ((1 : ℝ) / 10) < k)
    (T : ℝ) (hT : 1 < T) (hTx : T + h ≤ x) (L U : ℝ)
    (hL : L ≤ primeShiftSiftedSum h x P)
    (hU : (∑ k ∈ K, primeShiftSiftedSumAt h x k P) ≤ U) :
    L / Real.log x - (1 / 2) * (U / T.log) - 5 * (⌈T⌉₊ : ℝ) ≤
      primeShiftWeightedCount h x P K := by
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  have hlogT := Real.log_pos hT
  have hmain := (div_le_div_of_nonneg_right hL hlogx.le).trans
    (primeShiftSiftedSum_div_log_le_card h x hx P)
  have hu := sum_le_sum (fun k (_ : k ∈ K) => primeShiftSiftedPrimesAt_card_le h x k P T hT)
  rw [sum_add_distrib, ← sum_div] at hu
  have hsmall : (∑ k ∈ K,
      (((primeShiftSiftedPrimesAt h x k P).filter (fun p : ℕ => (p : ℝ) < T)).card : ℝ)) ≤
      10 * (⌈T⌉₊ : ℝ) := by
    exact_mod_cast sum_primeShift_small_card_le h x hx P K hK hlarge T hTx
  have hupper := hu.trans (_root_.add_le_add
    (div_le_div_of_nonneg_right hU hlogT.le) hsmall)
  unfold primeShiftWeightedCount
  linarith

end Chen.LinearSieve
