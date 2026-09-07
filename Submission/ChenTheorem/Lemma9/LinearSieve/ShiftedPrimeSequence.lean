import Submission.ChenTheorem.Lemma9.LinearSieve.PrimeSequence

set_option autoImplicit true
open Finset
open scoped Classical

namespace Chen.LinearSieve

/-- A natural-number representative of `-h` modulo `d`. It may equal
`d`; the progression estimates allow arbitrary representatives. -/
def negativeResidue (h d : ℕ) : ℕ := d - h % d

theorem negativeResidue_add_modEq_zero (h d : ℕ) (hd : 0 < d) :
    negativeResidue h d + h ≡ 0 [MOD d] := by
  apply Nat.modEq_zero_iff_dvd.mpr
  have hm := Nat.mod_add_div h d
  have hr := Nat.mod_lt h hd
  have heq : negativeResidue h d + h = d * (h / d) + d := by
    unfold negativeResidue
    omega
  rw [heq]
  exact dvd_add (dvd_mul_right d (h / d)) (dvd_refl d)

theorem dvd_add_iff_modEq_negativeResidue (h p d : ℕ) (hd : 0 < d) :
    d ∣ p + h ↔ p ≡ negativeResidue h d [MOD d] := by
  have hz := negativeResidue_add_modEq_zero h d hd
  constructor
  · intro hp
    exact Nat.ModEq.add_right_cancel' h ((Nat.modEq_zero_iff_dvd.mpr hp).trans hz.symm)
  · intro hp
    exact Nat.modEq_zero_iff_dvd.mp ((hp.add_right h).trans hz)

theorem negativeResidue_coprime (h d : ℕ) (hd : 0 < d) (hcop : h.Coprime d) :
    (negativeResidue h d).Coprime d := by
  unfold negativeResidue
  rw [Nat.coprime_self_sub_left (Nat.mod_lt h hd).le]
  have he : h % d ≡ h [MOD d] := by simp [Nat.ModEq]
  change Nat.gcd (h % d) d = 1
  rw [he.gcd_eq]
  exact hcop

/-- The logarithmic sequence `p+h`, for primes `p ≤ x`. The residue
parameter `h` is independent of the scale `x`. -/
noncomputable def primeShiftSieve (h x : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p) : BoundingSieve :=
  { primeDifferenceSieve x P hP hodd with
    support := (Icc 1 x).image (fun p => p + h)
    weights := fun n => primeDifferenceWeight n h
    weights_nonneg := fun n => primeDifferenceWeight_nonneg n h }

theorem sum_primeShift_support (h x : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ (Icc 1 x).image (fun p => p + h), f n) =
      ∑ p ∈ Icc 1 x, f (p + h) := by
  apply sum_image
  intro p _ q _ hpq
  exact Nat.add_right_cancel hpq

/-- The exact remainder progression for the translated sequence. -/
theorem primeShiftSieve_multSum (h x : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p)
    (d : ℕ) (hd : 0 < d) :
    (primeShiftSieve h x P hP hodd).multSum d =
      BombieriVinogradov.progressionTheta x d (negativeResidue h d) := by
  change (∑ n ∈ (Icc 1 x).image (fun p => p + h),
    if d ∣ n then primeDifferenceWeight n h else 0) = _
  rw [sum_primeShift_support]
  apply sum_congr rfl
  intro p _
  simp only [primeDifferenceWeight, Nat.add_sub_cancel,
    dvd_add_iff_modEq_negativeResidue h p d hd]
  split_ifs <;> simp_all

theorem primeShiftSieve_rem (h x : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p)
    (d : ℕ) (hd : 0 < d) :
    (primeShiftSieve h x P hP hodd).rem d =
      BombieriVinogradov.progressionTheta x d (negativeResidue h d) -
        (x : ℝ) / Nat.totient d := by
  rw [BoundingSieve.rem, primeShiftSieve_multSum h x P hP hodd d hd]
  simp [primeShiftSieve, primeDifferenceSieve, div_eq_mul_inv, mul_comm]

noncomputable def primeShiftSiftedSum (h x : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ Icc 1 x, if p.Prime ∧ (∏ r ∈ P, r).Coprime (p + h)
    then Real.log p else 0

theorem primeShiftSieve_siftedSum (h x : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p) :
    (primeShiftSieve h x P hP hodd).siftedSum = primeShiftSiftedSum h x P := by
  change (∑ n ∈ (Icc 1 x).image (fun p => p + h),
    if (∏ r ∈ P, r).Coprime n then primeDifferenceWeight n h else 0) = _
  rw [sum_primeShift_support]
  apply sum_congr rfl
  intro p _
  simp only [primeDifferenceWeight, Nat.add_sub_cancel]
  split_ifs <;> simp_all

theorem primeShift_rosser_bounds (h x : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p)
    (hcop : h.Coprime (∏ p ∈ P, p))
    (z : ℕ) (hz : ∀ p ∈ P, p < z) (D : ℝ) (hD : 1 < D)
    (Q : ℕ) (hDQ : D ≤ Q) :
    (x : ℝ) * rosserEval P primeDensity z false D -
        (∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d (negativeResidue h d)) ≤
      primeShiftSiftedSum h x P ∧
    primeShiftSiftedSum h x P ≤
      (x : ℝ) * rosserEval P primeDensity z true D +
        (∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d (negativeResidue h d)) := by
  have hb := rosser_sieve_bounds_of_remainders
    (primeShiftSieve h x P hP hodd) P hP rfl z hz D hD Q hDQ
    (fun d => BombieriVinogradov.reducedThetaError x d (negativeResidue h d))
    (fun d => BombieriVinogradov.reducedThetaError_nonneg x d (negativeResidue h d)) ?_
  · rw [primeShiftSieve_siftedSum] at hb
    simpa only [primeShiftSieve, primeDifferenceSieve] using hb
  · intro d hd _
    have hdpos := Nat.pos_of_mem_divisors hd
    have hdcop := negativeResidue_coprime h d hdpos
      (hcop.of_dvd_right (Nat.mem_divisors.mp hd).1)
    rw [primeShiftSieve_rem h x P hP hodd d hdpos]
    dsimp only [BombieriVinogradov.reducedThetaError]
    rw [if_pos hdcop]

end Chen.LinearSieve
