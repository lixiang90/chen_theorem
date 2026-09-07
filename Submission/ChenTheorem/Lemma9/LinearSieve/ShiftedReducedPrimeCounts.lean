import Submission.ChenTheorem.Lemma9.LinearSieve.ShiftedLogWeights

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

theorem primeShiftSiftedPrimes_mono (h x : ℕ) {P R : Finset ℕ} (hPR : P ⊆ R) :
    primeShiftSiftedPrimes h x R ⊆ primeShiftSiftedPrimes h x P := by
  intro p hp
  obtain ⟨hpI, hpprime, hcop⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hpI, hpprime,
    hcop.of_dvd_left (prod_dvd_prod_of_subset P R id hPR)⟩

theorem prime_eq_of_dvd_shift {h p k : ℕ} (hp : p.Prime) (hk : k.Prime)
    (hkh : k ∣ h) (hkd : k ∣ p + h) : p = k := by
  have hkp : k ∣ p := by simpa only [Nat.add_sub_cancel] using Nat.dvd_sub hkd hkh
  exact ((Nat.prime_dvd_prime_iff_eq hk hp).mp hkp).symm

theorem primeShiftSiftedPrimes_reduced_subset (h x : ℕ) (hh : h ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    primeShiftSiftedPrimes h x (P.filter (fun r => ¬r ∣ h)) ⊆
      primeShiftSiftedPrimes h x P ∪ h.primeFactors := by
  intro p hp
  obtain ⟨hpI, hpprime, hcop⟩ := mem_filter.mp hp
  by_cases hpf : p ∈ h.primeFactors
  · exact mem_union_right _ hpf
  apply mem_union_left
  refine mem_filter.mpr ⟨hpI, hpprime, Nat.coprime_prod_left_iff.mpr ?_⟩
  intro r hr
  apply (hP r hr).coprime_iff_not_dvd.mpr
  intro hrd
  by_cases hrh : r ∣ h
  · have hpr := prime_eq_of_dvd_shift hpprime (hP r hr) hrh hrd
    exact hpf (Nat.mem_primeFactors.mpr ⟨hpprime, hpr.symm ▸ hrh, hh⟩)
  · have hrcop := Nat.coprime_prod_left_iff.mp hcop r (mem_filter.mpr ⟨hr, hrh⟩)
    exact (hP r hr).coprime_iff_not_dvd.mp hrcop hrd

theorem primeShiftSiftedPrimes_reduced_card_le (h x : ℕ) (hh : h ≠ 0)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (primeShiftSiftedPrimes h x (P.filter (fun r => ¬r ∣ h))).card ≤
      (primeShiftSiftedPrimes h x P).card + h.primeFactors.card :=
  (card_le_card (primeShiftSiftedPrimes_reduced_subset h x hh P hP)).trans (card_union_le _ _)

theorem primeShiftSiftedPrimesAt_card_le_one (h x k : ℕ) (P : Finset ℕ)
    (hk : k.Prime) (hkh : k ∣ h) : (primeShiftSiftedPrimesAt h x k P).card ≤ 1 := by
  apply (card_le_card (show primeShiftSiftedPrimesAt h x k P ⊆ {k} from ?_)).trans_eq
    (card_singleton k)
  intro p hp
  obtain ⟨hpS, hkd⟩ := mem_filter.mp hp
  obtain ⟨_, hpprime, _⟩ := mem_filter.mp hpS
  exact mem_singleton.mpr (prime_eq_of_dvd_shift hpprime hk hkh hkd)

theorem sum_primeShiftSiftedPrimesAt_reduced_le (h x : ℕ) (hh : h ≠ 0)
    (P K : Finset ℕ) (hK : ∀ k ∈ K, Nat.Prime k) :
    (∑ k ∈ K, (primeShiftSiftedPrimesAt h x k P).card) ≤
      (∑ k ∈ K with ¬k ∣ h,
        (primeShiftSiftedPrimesAt h x k (P.filter (fun r => ¬r ∣ h))).card) +
      h.primeFactors.card := by
  have hbad : (K.filter (fun k => k ∣ h)).card ≤ h.primeFactors.card :=
    card_le_card (fun k hk => Nat.mem_primeFactors.mpr
      ⟨hK k (mem_filter.mp hk).1, (mem_filter.mp hk).2, hh⟩)
  calc
    _ ≤ ∑ k ∈ K,
        ((if ¬k ∣ h then (primeShiftSiftedPrimesAt h x k
          (P.filter (fun r => ¬r ∣ h))).card else 0) + if k ∣ h then 1 else 0) := by
      apply sum_le_sum
      intro k hk
      by_cases hkh : k ∣ h
      · simp only [hkh, not_true_eq_false, if_false, if_true, zero_add]
        exact primeShiftSiftedPrimesAt_card_le_one h x k P (hK k hk) hkh
      · simp only [hkh, not_false_eq_true, if_true, if_false, add_zero]
        apply card_le_card
        intro p hp
        obtain ⟨hpS, hkd⟩ := mem_filter.mp hp
        exact mem_filter.mpr ⟨primeShiftSiftedPrimes_mono h x (filter_subset _ _) hpS, hkd⟩
    _ = (∑ k ∈ K with ¬k ∣ h,
        (primeShiftSiftedPrimesAt h x k (P.filter (fun r => ¬r ∣ h))).card) +
        (K.filter (fun k => k ∣ h)).card := by
      rw [sum_add_distrib, ← sum_filter]
      simp
    _ ≤ _ := Nat.add_le_add_left hbad _

/-- Restoring all prime classes costs at most `3ω(h)/2`, a fixed
constant for the translated problem. -/
theorem primeShiftWeightedCount_reduced_le (h x : ℕ) (hh : h ≠ 0)
    (P K : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hK : ∀ k ∈ K, Nat.Prime k) :
    primeShiftWeightedCount h x (P.filter (fun r => ¬r ∣ h))
        (K.filter (fun k => ¬k ∣ h)) - (3 / 2) * h.primeFactors.card ≤
      primeShiftWeightedCount h x P K := by
  have hl : ((primeShiftSiftedPrimes h x (P.filter (fun r => ¬r ∣ h))).card : ℝ) ≤
      (primeShiftSiftedPrimes h x P).card + h.primeFactors.card := by
    exact_mod_cast primeShiftSiftedPrimes_reduced_card_le h x hh P hP
  have hu : (∑ k ∈ K, ((primeShiftSiftedPrimesAt h x k P).card : ℝ)) ≤
      (∑ k ∈ K with ¬k ∣ h,
        ((primeShiftSiftedPrimesAt h x k (P.filter (fun r => ¬r ∣ h))).card : ℝ)) +
      h.primeFactors.card := by
    exact_mod_cast sum_primeShiftSiftedPrimesAt_reduced_le h x hh P K hK
  unfold primeShiftWeightedCount
  linarith

end Chen.LinearSieve
