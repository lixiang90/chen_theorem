import Submission.ChenTheorem.Lemma9.LinearSieve.SmallPrimeLoss

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

theorem primeDifferenceSiftedPrimes_mono (x : ℕ) {P R : Finset ℕ} (hPR : P ⊆ R) :
    primeDifferenceSiftedPrimes x R ⊆ primeDifferenceSiftedPrimes x P := by
  intro p hp
  obtain ⟨hpI, hpprime, hcop⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hpI, hpprime,
    hcop.of_dvd_left (prod_dvd_prod_of_subset P R id hPR)⟩

/-- A non-reduced residue can contain only the prime dividing its modulus. -/
theorem prime_eq_of_dvd_difference {x p k : ℕ} (hp : p.Prime) (hk : k.Prime)
    (hpx : p ≤ x) (hkx : k ∣ x) (hkd : k ∣ x - p) : p = k := by
  have hkp : k ∣ p := by
    have h := Nat.dvd_sub hkx hkd
    simpa only [Nat.sub_sub_self hpx] using h
  exact ((Nat.prime_dvd_prime_iff_eq hk hp).mp hkp).symm

/-- Omitting sifting primes dividing `x` adds at most the prime divisors
of `x` to the sifted prime set. -/
theorem primeDifferenceSiftedPrimes_reduced_subset (x : ℕ) (hx : x ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    primeDifferenceSiftedPrimes x (P.filter (fun r => ¬r ∣ x)) ⊆
      primeDifferenceSiftedPrimes x P ∪ x.primeFactors := by
  intro p hp
  obtain ⟨hpI, hpprime, hcop⟩ := mem_filter.mp hp
  by_cases hpf : p ∈ x.primeFactors
  · exact mem_union_right _ hpf
  apply mem_union_left
  refine mem_filter.mpr ⟨hpI, hpprime, Nat.coprime_prod_left_iff.mpr ?_⟩
  intro r hr
  apply (hP r hr).coprime_iff_not_dvd.mpr
  intro hrd
  by_cases hrx : r ∣ x
  · have hpr := prime_eq_of_dvd_difference hpprime (hP r hr) (mem_Icc.mp hpI).2 hrx hrd
    exact hpf (Nat.mem_primeFactors.mpr ⟨hpprime, hpr.symm ▸ hrx, hx⟩)
  · have hrcop := Nat.coprime_prod_left_iff.mp hcop r (mem_filter.mpr ⟨hr, hrx⟩)
    exact (hP r hr).coprime_iff_not_dvd.mp hrcop hrd

theorem primeDifferenceSiftedPrimes_reduced_card_le (x : ℕ) (hx : x ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (primeDifferenceSiftedPrimes x (P.filter (fun r => ¬r ∣ x))).card ≤
      (primeDifferenceSiftedPrimes x P).card + x.primeFactors.card :=
  (card_le_card (primeDifferenceSiftedPrimes_reduced_subset x hx P hP)).trans (card_union_le _ _)

theorem primeDifferenceSiftedPrimesAt_card_le_one (x k : ℕ) (P : Finset ℕ)
    (hk : k.Prime) (hkx : k ∣ x) : (primeDifferenceSiftedPrimesAt x k P).card ≤ 1 := by
  apply (card_le_card (show primeDifferenceSiftedPrimesAt x k P ⊆ {k} from ?_)).trans_eq
    (card_singleton k)
  intro p hp
  obtain ⟨hpS, hkd⟩ := mem_filter.mp hp
  obtain ⟨hpI, hpprime, _⟩ := mem_filter.mp hpS
  exact mem_singleton.mpr (prime_eq_of_dvd_difference hpprime hk (mem_Icc.mp hpI).2 hkx hkd)

theorem sum_primeDifferenceSiftedPrimesAt_reduced_le (x : ℕ) (hx : x ≠ 0)
    (P K : Finset ℕ) (hK : ∀ k ∈ K, Nat.Prime k) :
    (∑ k ∈ K, (primeDifferenceSiftedPrimesAt x k P).card) ≤
      (∑ k ∈ K with ¬k ∣ x,
        (primeDifferenceSiftedPrimesAt x k (P.filter (fun r => ¬r ∣ x))).card) +
      x.primeFactors.card := by
  have hbad : (K.filter (fun k => k ∣ x)).card ≤ x.primeFactors.card :=
    card_le_card (fun k hk => Nat.mem_primeFactors.mpr
      ⟨hK k (mem_filter.mp hk).1, (mem_filter.mp hk).2, hx⟩)
  calc
    _ ≤ ∑ k ∈ K,
        ((if ¬k ∣ x then (primeDifferenceSiftedPrimesAt x k
          (P.filter (fun r => ¬r ∣ x))).card else 0) + if k ∣ x then 1 else 0) := by
      apply sum_le_sum
      intro k hk
      by_cases hkx : k ∣ x
      · simp only [hkx, not_true_eq_false, if_false, if_true, zero_add]
        exact primeDifferenceSiftedPrimesAt_card_le_one x k P (hK k hk) hkx
      · simp only [hkx, not_false_eq_true, if_true, if_false, add_zero]
        apply card_le_card
        intro p hp
        obtain ⟨hpS, hkd⟩ := mem_filter.mp hp
        exact mem_filter.mpr ⟨primeDifferenceSiftedPrimes_mono x (filter_subset _ _) hpS, hkd⟩
    _ = (∑ k ∈ K with ¬k ∣ x,
        (primeDifferenceSiftedPrimesAt x k (P.filter (fun r => ¬r ∣ x))).card) +
        (K.filter (fun k => k ∣ x)).card := by
      rw [sum_add_distrib, ← sum_filter]
      simp
    _ ≤ _ := Nat.add_le_add_left hbad _

/-- Returning the reduced-residue sieve to all original prime classes
costs only `3/2` times the number of distinct prime factors of `x`. -/
theorem primeDifferenceWeightedCount_reduced_le (x : ℕ) (hx : x ≠ 0)
    (P K : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hK : ∀ k ∈ K, Nat.Prime k) :
    primeDifferenceWeightedCount x (P.filter (fun r => ¬r ∣ x))
        (K.filter (fun k => ¬k ∣ x)) - (3 / 2) * x.primeFactors.card ≤
      primeDifferenceWeightedCount x P K := by
  have hl : ((primeDifferenceSiftedPrimes x (P.filter (fun r => ¬r ∣ x))).card : ℝ) ≤
      (primeDifferenceSiftedPrimes x P).card + x.primeFactors.card := by
    exact_mod_cast primeDifferenceSiftedPrimes_reduced_card_le x hx P hP
  have hu : (∑ k ∈ K, ((primeDifferenceSiftedPrimesAt x k P).card : ℝ)) ≤
      (∑ k ∈ K with ¬k ∣ x,
        ((primeDifferenceSiftedPrimesAt x k (P.filter (fun r => ¬r ∣ x))).card : ℝ)) +
      x.primeFactors.card := by
    exact_mod_cast sum_primeDifferenceSiftedPrimesAt_reduced_le x hx P K hK
  unfold primeDifferenceWeightedCount
  linarith

end Chen.LinearSieve
