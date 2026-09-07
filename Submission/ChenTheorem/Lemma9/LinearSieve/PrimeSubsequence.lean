import Submission.ChenTheorem.Lemma9.LinearSieve.PrimeSequence

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

/-- The difference sequence with the additional condition `k ∣ x - p`,
used for the middle-prime correction in Chen's weighted sieve. -/
noncomputable def primeDifferenceSubsequence (x k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p) : BoundingSieve :=
  { primeDifferenceSieve x P hP hodd with
    weights := fun n => if k ∣ n then primeDifferenceWeight x n else 0
    weights_nonneg := by
      intro n
      split_ifs
      · exact primeDifferenceWeight_nonneg x n
      · exact le_rfl
    totalMass := (x : ℝ) / Nat.totient k }

theorem primeDifferenceSubsequence_multSum (x k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p)
    (d : ℕ) (hdk : d.Coprime k) :
    (primeDifferenceSubsequence x k P hP hodd).multSum d =
      BombieriVinogradov.progressionTheta x (d * k) x := by
  rw [← primeDifferenceSieve_multSum x P hP hodd]
  apply sum_congr rfl
  intro n _
  have hdiv : d * k ∣ n ↔ d ∣ n ∧ k ∣ n :=
    ⟨fun h => ⟨dvd_trans (dvd_mul_right d k) h, dvd_trans (dvd_mul_left k d) h⟩,
      fun h => hdk.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  change (if d ∣ n then (if k ∣ n then primeDifferenceWeight x n else 0) else 0) =
    if d * k ∣ n then primeDifferenceWeight x n else 0
  simp only [hdiv]
  split_ifs <;> simp_all

theorem primeDifferenceSubsequence_rem (x k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p)
    (d : ℕ) (hdk : d.Coprime k) :
    (primeDifferenceSubsequence x k P hP hodd).rem d =
      BombieriVinogradov.progressionTheta x (d * k) x -
        (x : ℝ) / Nat.totient (d * k) := by
  rw [BoundingSieve.rem, primeDifferenceSubsequence_multSum x k P hP hodd d hdk]
  simp [primeDifferenceSubsequence, primeDifferenceSieve,
    Nat.totient_mul hdk, div_eq_mul_inv]
  ring

/-- The logarithmically weighted middle-prime correction. -/
noncomputable def primeDifferenceSiftedSumAt (x k : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ Icc 1 x,
    if p.Prime ∧ k ∣ x - p ∧ (∏ r ∈ P, r).Coprime (x - p)
    then Real.log p else 0

theorem primeDifferenceSubsequence_siftedSum (x k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p) :
    (primeDifferenceSubsequence x k P hP hodd).siftedSum =
      primeDifferenceSiftedSumAt x k P := by
  change (∑ n ∈ (Icc 1 x).image (fun p => x - p),
    if (∏ r ∈ P, r).Coprime n then
      (if k ∣ n then primeDifferenceWeight x n else 0) else 0) = _
  rw [sum_primeDifference_support]
  apply sum_congr rfl
  intro p hp
  have hsub : x - (x - p) = p := by have := (mem_Icc.mp hp).2; omega
  simp only [primeDifferenceWeight, hsub]
  split_ifs <;> simp_all

/-- The correction sequence has the expected density `x / φ(k)` and
progression remainders at moduli `d*k`. This finite inequality is ready for
the subsequent sum over middle primes. -/
theorem primeDifferenceSubsequence_rosser_bounds (x k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p)
    (hcop : x.Coprime ((∏ p ∈ P, p) * k))
    (hkcop : k.Coprime (∏ p ∈ P, p))
    (z : ℕ) (hz : ∀ p ∈ P, p < z) (D : ℝ) (hD : 1 < D)
    (Q : ℕ) (hDQ : D ≤ Q) :
    ((x : ℝ) / Nat.totient k) * rosserEval P primeDensity z false D -
        (∑ d ∈ (∏ p ∈ P, p).divisors with d ≤ Q,
          BombieriVinogradov.reducedThetaError x (d * k) x) ≤
      primeDifferenceSiftedSumAt x k P ∧
    primeDifferenceSiftedSumAt x k P ≤
      ((x : ℝ) / Nat.totient k) * rosserEval P primeDensity z true D +
        (∑ d ∈ (∏ p ∈ P, p).divisors with d ≤ Q,
          BombieriVinogradov.reducedThetaError x (d * k) x) := by
  have hb := rosser_sieve_bounds_of_divisor_remainders
    (primeDifferenceSubsequence x k P hP hodd) P hP rfl z hz D hD Q hDQ
    (fun d => BombieriVinogradov.reducedThetaError x (d * k) x)
    ?_
  · rw [primeDifferenceSubsequence_siftedSum] at hb
    simpa only [primeDifferenceSubsequence, primeDifferenceSieve] using hb
  · intro d hd _
    have hdvd : d ∣ ∏ p ∈ P, p := (Nat.mem_divisors.mp hd).1
    have hdk : d.Coprime k := (hkcop.of_dvd_right hdvd).symm
    have hdcop : x.Coprime (d * k) := hcop.of_dvd_right (Nat.mul_dvd_mul hdvd (dvd_refl k))
    rw [primeDifferenceSubsequence_rem x k P hP hodd d hdk]
    dsimp only [BombieriVinogradov.reducedThetaError]
    rw [if_pos hdcop]

end Chen.LinearSieve
