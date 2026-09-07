import Submission.ChenTheorem.Lemma9.LinearSieve.ShiftedPrimeSequence

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

noncomputable def primeShiftSubsequence (h x k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p) : BoundingSieve :=
  { primeShiftSieve h x P hP hodd with
    weights := fun n => if k ∣ n then primeDifferenceWeight n h else 0
    weights_nonneg := by
      intro n
      split_ifs
      · exact primeDifferenceWeight_nonneg n h
      · exact le_rfl
    totalMass := (x : ℝ) / Nat.totient k }

theorem primeShiftSubsequence_multSum (h x k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p)
    (d : ℕ) (hdk : d.Coprime k) (hdkpos : 0 < d * k) :
    (primeShiftSubsequence h x k P hP hodd).multSum d =
      BombieriVinogradov.progressionTheta x (d * k) (negativeResidue h (d * k)) := by
  rw [← primeShiftSieve_multSum h x P hP hodd (d * k) hdkpos]
  apply sum_congr rfl
  intro n _
  have hdiv : d * k ∣ n ↔ d ∣ n ∧ k ∣ n :=
    ⟨fun h => ⟨dvd_trans (dvd_mul_right d k) h, dvd_trans (dvd_mul_left k d) h⟩,
      fun h => hdk.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  change (if d ∣ n then (if k ∣ n then primeDifferenceWeight n h else 0) else 0) =
    if d * k ∣ n then primeDifferenceWeight n h else 0
  simp only [hdiv]
  split_ifs <;> simp_all

theorem primeShiftSubsequence_rem (h x k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p)
    (d : ℕ) (hdk : d.Coprime k) (hdkpos : 0 < d * k) :
    (primeShiftSubsequence h x k P hP hodd).rem d =
      BombieriVinogradov.progressionTheta x (d * k) (negativeResidue h (d * k)) -
        (x : ℝ) / Nat.totient (d * k) := by
  rw [BoundingSieve.rem, primeShiftSubsequence_multSum h x k P hP hodd d hdk hdkpos]
  simp [primeShiftSubsequence, primeShiftSieve, primeDifferenceSieve,
    Nat.totient_mul hdk, div_eq_mul_inv]
  ring

noncomputable def primeShiftSiftedSumAt (h x k : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ Icc 1 x,
    if p.Prime ∧ k ∣ p + h ∧ (∏ r ∈ P, r).Coprime (p + h)
    then Real.log p else 0

theorem primeShiftSubsequence_siftedSum (h x k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p) :
    (primeShiftSubsequence h x k P hP hodd).siftedSum =
      primeShiftSiftedSumAt h x k P := by
  change (∑ n ∈ (Icc 1 x).image (fun p => p + h),
    if (∏ r ∈ P, r).Coprime n then
      (if k ∣ n then primeDifferenceWeight n h else 0) else 0) = _
  rw [sum_primeShift_support]
  apply sum_congr rfl
  intro p _
  simp only [primeDifferenceWeight, Nat.add_sub_cancel]
  split_ifs <;> simp_all

/-- The fixed middle-prime contribution has density `x / φ(k)` and
exact remainders in the progression `-h mod d*k`. The sum retains the
actual divisor support needed for multiplicity-one BV control. -/
theorem primeShiftSubsequence_rosser_bounds (h x k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p)
    (hkpos : 0 < k) (hcop : h.Coprime ((∏ p ∈ P, p) * k))
    (hkcop : k.Coprime (∏ p ∈ P, p))
    (z : ℕ) (hz : ∀ p ∈ P, p < z) (D : ℝ) (hD : 1 < D)
    (Q : ℕ) (hDQ : D ≤ Q) :
    ((x : ℝ) / Nat.totient k) * rosserEval P primeDensity z false D -
        (∑ d ∈ (∏ p ∈ P, p).divisors with d ≤ Q,
          BombieriVinogradov.reducedThetaError x (d * k) (negativeResidue h (d * k))) ≤
      primeShiftSiftedSumAt h x k P ∧
    primeShiftSiftedSumAt h x k P ≤
      ((x : ℝ) / Nat.totient k) * rosserEval P primeDensity z true D +
        (∑ d ∈ (∏ p ∈ P, p).divisors with d ≤ Q,
          BombieriVinogradov.reducedThetaError x (d * k) (negativeResidue h (d * k))) := by
  have hb := rosser_sieve_bounds_of_divisor_remainders
    (primeShiftSubsequence h x k P hP hodd) P hP rfl z hz D hD Q hDQ
    (fun d => BombieriVinogradov.reducedThetaError x (d * k) (negativeResidue h (d * k))) ?_
  · rw [primeShiftSubsequence_siftedSum] at hb
    simpa only [primeShiftSubsequence, primeShiftSieve, primeDifferenceSieve] using hb
  · intro d hd _
    have hdvd : d ∣ ∏ p ∈ P, p := (Nat.mem_divisors.mp hd).1
    have hdk : d.Coprime k := (hkcop.of_dvd_right hdvd).symm
    have hdkpos := Nat.mul_pos (Nat.pos_of_mem_divisors hd) hkpos
    have hdcop := negativeResidue_coprime h (d * k) hdkpos
      (hcop.of_dvd_right (Nat.mul_dvd_mul hdvd (dvd_refl k)))
    rw [primeShiftSubsequence_rem h x k P hP hodd d hdk hdkpos]
    dsimp only [BombieriVinogradov.reducedThetaError]
    rw [if_pos hdcop]

end Chen.LinearSieve
