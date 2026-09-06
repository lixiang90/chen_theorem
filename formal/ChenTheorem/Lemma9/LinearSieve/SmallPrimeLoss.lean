import ChenTheorem.Lemma9.LinearSieve.LogWeights
import Mathlib.RingTheory.Coprime.Lemmas

open Finset
open scoped Classical

namespace Chen.LinearSieve

/-- A nonzero integer at most `x` has at most ten distinct prime divisors
exceeding `x^(1/10)`. This applies to the whole middle-prime interval. -/
theorem card_large_prime_divisors_le_ten (S : Finset ℕ) (x m : ℕ)
    (hx : 1 < x) (hm : 0 < m) (hmx : m ≤ x)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hdiv : ∀ p ∈ S, p ∣ m)
    (hlarge : ∀ p ∈ S, (x : ℝ) ^ ((1 : ℝ) / 10) < p) : S.card ≤ 10 := by
  have hproddiv : (∏ p ∈ S, p) ∣ m := Finset.prod_dvd_of_isRelPrime
    (fun p hp q hq hpq => Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)) hdiv
  have hprodpos : 0 < ∏ p ∈ S, p := prod_pos (fun p hp => (hprime p hp).pos)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  have hsumle : (∑ p ∈ S, Real.log p) ≤ Real.log x := by
    calc
      _ = Real.log ((∏ p ∈ S, p : ℕ) : ℝ) := by
        rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hprime p hp).ne_zero)]
      _ ≤ _ := Real.log_le_log (by exact_mod_cast hprodpos)
        (by exact_mod_cast (Nat.le_of_dvd hm hproddiv).trans hmx)
  have hsumge : ((1 : ℝ) / 10) * Real.log x * S.card ≤ ∑ p ∈ S, Real.log p := by
    calc
      _ = ∑ _p ∈ S, ((1 : ℝ) / 10) * Real.log x := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun p hp => by
        have h := Real.log_le_log (Real.rpow_pos_of_pos hxpos ((1 : ℝ) / 10)) (hlarge p hp).le
        simpa only [Real.log_rpow hxpos] using h)
  have : (S.card : ℝ) ≤ 10 := by nlinarith
  exact_mod_cast this

theorem sum_card_filter_comm (K S : Finset ℕ) (R : ℕ → ℕ → Prop) :
    (∑ k ∈ K, (S.filter (R k)).card) =
      ∑ p ∈ S, (K.filter (fun k => R k p)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  exact sum_comm

/-- Aggregate small-prime correction loss, before estimating it. -/
noncomputable def smallPrimeCorrectionCount (x : ℕ) (P K : Finset ℕ) (T : ℝ) : ℕ :=
  ∑ k ∈ K, ((primeDifferenceSiftedPrimesAt x k P).filter
    (fun p : ℕ => (p : ℝ) < T)).card

theorem smallPrimeCorrectionCount_eq (x : ℕ) (P K : Finset ℕ) (T : ℝ) :
    smallPrimeCorrectionCount x P K T =
      ∑ p ∈ (primeDifferenceSiftedPrimes x P).filter (fun p : ℕ => (p : ℝ) < T),
        (K.filter (fun k => k ∣ x - p)).card := by
  unfold smallPrimeCorrectionCount primeDifferenceSiftedPrimesAt
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  by_cases hp : (p : ℝ) < T
  · simp only [if_pos hp]
  · simp only [if_neg hp]
    apply sum_eq_zero
    intro k _
    split_ifs <;> simp_all

/-- The total small-prime loss is `O(T)`, uniformly in the middle-prime
set. The nonprime endpoint hypothesis excludes `x-p=0`. -/
theorem smallPrimeCorrectionCount_le (x : ℕ) (hx : 1 < x) (hxnp : ¬x.Prime)
    (P K : Finset ℕ) (hK : ∀ k ∈ K, Nat.Prime k)
    (hlarge : ∀ k ∈ K, (x : ℝ) ^ ((1 : ℝ) / 10) < k) (T : ℝ) :
    smallPrimeCorrectionCount x P K T ≤ 10 * ⌈T⌉₊ := by
  rw [smallPrimeCorrectionCount_eq]
  let S := (primeDifferenceSiftedPrimes x P).filter (fun p : ℕ => (p : ℝ) < T)
  have hmult (p : ℕ) (hp : p ∈ S) : (K.filter (fun k => k ∣ x - p)).card ≤ 10 := by
    have hpS := (mem_filter.mp hp).1
    have hpp : p.Prime := (mem_filter.mp hpS).2.1
    have hpx : p ≤ x := (mem_Icc.mp (mem_filter.mp hpS).1).2
    have hne : p ≠ x := by rintro rfl; exact hxnp hpp
    exact card_large_prime_divisors_le_ten _ x (x - p) hx (by omega) (Nat.sub_le _ _)
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

/-- The ordinary-count counterpart of the weighted sieve expression. -/
noncomputable def primeDifferenceWeightedCount (x : ℕ) (P K : Finset ℕ) : ℝ :=
  (primeDifferenceSiftedPrimes x P).card -
    (1 / 2) * ∑ k ∈ K, ((primeDifferenceSiftedPrimesAt x k P).card : ℝ)

/-- Convert separate logarithmically weighted main/correction estimates
to ordinary counts. The whole correction loses at most `5 * ceil T`,
independently of the number of middle primes. -/
theorem primeDifference_count_lower_of_log_bounds (x : ℕ)
    (hx : 1 < x) (hxnp : ¬x.Prime) (P K : Finset ℕ)
    (hK : ∀ k ∈ K, Nat.Prime k)
    (hlarge : ∀ k ∈ K, (x : ℝ) ^ ((1 : ℝ) / 10) < k)
    (T : ℝ) (hT : 1 < T) (L U : ℝ)
    (hL : L ≤ primeDifferenceSiftedSum x P)
    (hU : (∑ k ∈ K, primeDifferenceSiftedSumAt x k P) ≤ U) :
    L / Real.log x - (1 / 2) * (U / T.log) - 5 * (⌈T⌉₊ : ℝ) ≤
      primeDifferenceWeightedCount x P K := by
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  have hlogT := Real.log_pos hT
  have hmain := (div_le_div_of_nonneg_right hL hlogx.le).trans
    (primeDifferenceSiftedSum_div_log_le_card x hx P)
  have hu := sum_le_sum (fun k (_ : k ∈ K) =>
    primeDifferenceSiftedPrimesAt_card_le x k P T hT)
  rw [sum_add_distrib, ← sum_div] at hu
  have hsmall : (∑ k ∈ K,
      (((primeDifferenceSiftedPrimesAt x k P).filter (fun p : ℕ => (p : ℝ) < T)).card : ℝ)) ≤
      10 * (⌈T⌉₊ : ℝ) := by
    exact_mod_cast smallPrimeCorrectionCount_le x hx hxnp P K hK hlarge T
  have hupper := hu.trans (_root_.add_le_add
    (div_le_div_of_nonneg_right hU hlogT.le) hsmall)
  unfold primeDifferenceWeightedCount
  linarith

end Chen.LinearSieve
