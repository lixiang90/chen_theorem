import Submission.ChenTheorem.Lemma9.LinearSieve.ShiftedReducedPrimeCounts
import Submission.ChenTheorem.Lemma9.LinearSieve.ChenPrimeCounts
import Submission.ChenTheorem.Main.ShiftedDefs

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

theorem shiftedSievedPrimeCount_eq_card (h x : ℕ) (hx : 1 ≤ x) :
    shiftedSievedPrimeCount h x = (primeShiftSiftedPrimes h x (chenSmallPrimes x)).card := by
  unfold shiftedSievedPrimeCount primeShiftSiftedPrimes
  congr 1
  ext p
  simp only [mem_filter, mem_range, mem_Icc, coprime_chenSmallPrimes_iff x hx]
  constructor
  · rintro ⟨hp, hprime, hsieve⟩
    exact ⟨⟨hprime.one_le, by omega⟩, hprime, hsieve⟩
  · rintro ⟨⟨_, hp⟩, hprime, hsieve⟩
    exact ⟨by omega, hprime, hsieve⟩

theorem shiftedSievedPrimeCountAt_eq_card (h x k : ℕ) (hx : 1 ≤ x) :
    shiftedSievedPrimeCountAt h x k =
      (primeShiftSiftedPrimesAt h x k (chenSmallPrimes x)).card := by
  unfold shiftedSievedPrimeCountAt primeShiftSiftedPrimesAt primeShiftSiftedPrimes
  congr 1
  ext p
  simp only [mem_filter, mem_range, mem_Icc, coprime_chenSmallPrimes_iff x hx]
  constructor
  · rintro ⟨hp, hprime, hkd, hsieve⟩
    exact ⟨⟨⟨hprime.one_le, by omega⟩, hprime, hsieve⟩, hkd⟩
  · rintro ⟨⟨⟨_, hp⟩, hprime, hsieve⟩, hkd⟩
    exact ⟨by omega, hprime, hkd, hsieve⟩

noncomputable abbrev chenShiftedSmallPrimes (h x : ℕ) : Finset ℕ :=
  (chenSmallPrimes x).filter (fun r => ¬r ∣ h)

noncomputable abbrev chenShiftedMidPrimes (h x : ℕ) : Finset ℕ :=
  (midPrimes x).filter (fun k => ¬k ∣ h)

/-- Count conversion for the actual fixed-shift quantities in the
project, including the bounded loss from non-reduced classes. -/
theorem shifted_chen_count_lower_of_log_bounds (h x : ℕ) (hh : h ≠ 0) (hx : 1 < x)
    (T : ℝ) (hT : 1 < T) (hTx : T + h ≤ x) (L U : ℝ)
    (hL : L ≤ primeShiftSiftedSum h x (chenShiftedSmallPrimes h x))
    (hU : (∑ k ∈ chenShiftedMidPrimes h x,
      primeShiftSiftedSumAt h x k (chenShiftedSmallPrimes h x)) ≤ U) :
    L / Real.log x - (1 / 2) * (U / T.log) - 5 * (⌈T⌉₊ : ℝ) -
        (3 / 2) * h.primeFactors.card ≤
      (shiftedSievedPrimeCount h x : ℝ) -
        (1 / 2) * ∑ k ∈ midPrimes x, (shiftedSievedPrimeCountAt h x k : ℝ) := by
  have hK : ∀ k ∈ midPrimes x, Nat.Prime k := fun k hk => (mem_filter.mp hk).2.1
  have hlarge : ∀ k ∈ chenShiftedMidPrimes h x,
      (x : ℝ) ^ ((1 : ℝ) / 10) < k := by
    intro k hk
    exact (mem_filter.mp (mem_filter.mp hk).1).2.2.1
  have hc := primeShift_count_lower_of_log_bounds h x hx
    (chenShiftedSmallPrimes h x) (chenShiftedMidPrimes h x)
    (fun k hk => hK k (mem_filter.mp hk).1) hlarge T hT hTx L U hL hU
  have hr := primeShiftWeightedCount_reduced_le h x hh (chenSmallPrimes x)
    (midPrimes x) (chenSmallPrimes_prime x) hK
  have hb := (sub_le_sub_right hc ((3 / 2) * (h.primeFactors.card : ℝ))).trans hr
  simpa only [primeShiftWeightedCount, shiftedSievedPrimeCount_eq_card h x hx.le,
    shiftedSievedPrimeCountAt_eq_card h x _ hx.le] using hb

/-- A constructed finite Rosser bound for the exact fixed-shift counts.
The shift appears only in the omitted prime classes and the progression
representatives; the density and sieve polynomials are unchanged. -/
theorem shifted_chen_count_lower_of_rosser_polynomials
    (h x : ℕ) (hh : h ≠ 0) (hx : 1 < x)
    (T : ℝ) (hT : 1 < T) (hTx : T + h ≤ x)
    (z : ℕ) (hz : ∀ p ∈ chenShiftedSmallPrimes h x, p < z)
    (Q : ℕ) (D : ℝ) (hD : 1 < D) (hDQ : D ≤ Q)
    (DAt : ℕ → ℝ) (hDAt : ∀ k ∈ chenShiftedMidPrimes h x, 1 < DAt k)
    (hDAtQ : ∀ k ∈ chenShiftedMidPrimes h x, DAt k ≤ (Q / k : ℕ)) :
    (((x : ℝ) * rosserEval (chenShiftedSmallPrimes h x) primeDensity z false D -
        ∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d (negativeResidue h d)) / Real.log x) -
      (1 / 2) * (((∑ k ∈ chenShiftedMidPrimes h x,
        ((x : ℝ) / Nat.totient k) *
          rosserEval (chenShiftedSmallPrimes h x) primeDensity z true (DAt k)) +
        ∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d (negativeResidue h d)) / T.log) -
      5 * (⌈T⌉₊ : ℝ) - (3 / 2) * h.primeFactors.card ≤
      (shiftedSievedPrimeCount h x : ℝ) -
        (1 / 2) * ∑ k ∈ midPrimes x, (shiftedSievedPrimeCountAt h x k : ℝ) := by
  have hP : ∀ p ∈ chenShiftedSmallPrimes h x, Nat.Prime p :=
    fun p hp => chenSmallPrimes_prime x p (mem_filter.mp hp).1
  have hodd : ∀ p ∈ chenShiftedSmallPrimes h x, 2 < p :=
    fun p hp => ((mem_chenSmallPrimes hx.le).mp (mem_filter.mp hp).1).2.1
  have hK : ∀ k ∈ chenShiftedMidPrimes h x, Nat.Prime k :=
    fun k hk => (mem_filter.mp (mem_filter.mp hk).1).2.1
  have hsep : ∀ p ∈ chenShiftedSmallPrimes h x, ∀ k ∈ chenShiftedMidPrimes h x, p < k := by
    intro p hp k hk
    have hpSmall := ((mem_chenSmallPrimes hx.le).mp (mem_filter.mp hp).1).2.2
    have hkLarge := (mem_filter.mp (mem_filter.mp hk).1).2.2.1
    exact_mod_cast lt_of_le_of_lt hpSmall hkLarge
  have hcopP : h.Coprime (∏ p ∈ chenShiftedSmallPrimes h x, p) :=
    Nat.coprime_prod_right_iff.mpr (fun p hp =>
      ((hP p hp).coprime_iff_not_dvd.mpr (mem_filter.mp hp).2).symm)
  have hcopK : ∀ k ∈ chenShiftedMidPrimes h x, h.Coprime k :=
    fun k hk => ((hK k hk).coprime_iff_not_dvd.mpr (mem_filter.mp hk).2).symm
  obtain ⟨hlower, hupper⟩ := primeShift_rosser_main_and_correction h x
    (chenShiftedSmallPrimes h x) (chenShiftedMidPrimes h x) hP hodd hK hsep hcopP hcopK
    z hz Q D hD hDQ DAt hDAt hDAtQ
  exact shifted_chen_count_lower_of_log_bounds h x hh hx T hT hTx _ _ hlower hupper

end Chen.LinearSieve
