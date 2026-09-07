import Submission.ChenTheorem.Lemma9.LinearSieve.ShiftedPrimeSubsequence
import Submission.ChenTheorem.Lemma9.LinearSieve.MiddlePrimeErrors

set_option autoImplicit true
open Finset Filter
open scoped Classical

namespace Chen.LinearSieve

/-- Separate finite bounds for the main translated sequence and the
total middle-prime correction. Their progression errors share a single
BV sum, with no added divisor multiplicity. -/
theorem primeShift_rosser_main_and_correction (h x : ℕ) (P K : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p)
    (hK : ∀ k ∈ K, Nat.Prime k) (hsep : ∀ p ∈ P, ∀ k ∈ K, p < k)
    (hcopP : h.Coprime (∏ p ∈ P, p)) (hcopK : ∀ k ∈ K, h.Coprime k)
    (z : ℕ) (hz : ∀ p ∈ P, p < z)
    (Q : ℕ) (D : ℝ) (hD : 1 < D) (hDQ : D ≤ Q)
    (DAt : ℕ → ℝ) (hDAt : ∀ k ∈ K, 1 < DAt k)
    (hDAtQ : ∀ k ∈ K, DAt k ≤ (Q / k : ℕ)) :
    (x : ℝ) * rosserEval P primeDensity z false D -
        (∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d (negativeResidue h d)) ≤
        primeShiftSiftedSum h x P ∧
      (∑ k ∈ K, primeShiftSiftedSumAt h x k P) ≤
        (∑ k ∈ K, ((x : ℝ) / Nat.totient k) * rosserEval P primeDensity z true (DAt k)) +
        (∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d (negativeResidue h d)) := by
  have hlower := (primeShift_rosser_bounds h x P hP hodd hcopP z hz D hD Q hDQ).1
  have hupper (k : ℕ) (hk : k ∈ K) :=
    (primeShiftSubsequence_rosser_bounds h x k P hP hodd (hK k hk).pos
      (hcopP.mul_right (hcopK k hk))
      (show k.Coprime (∏ p ∈ P, p) from Nat.coprime_prod_right_iff.mpr (fun p hp =>
        (Nat.coprime_primes (hK k hk) (hP p hp)).mpr (ne_of_gt (hsep p hp k hk))))
      z hz (DAt k) (hDAt k hk) (Q / k) (hDAtQ k hk)).2
  have herr : (∑ k ∈ K, ∑ d ∈ (∏ p ∈ P, p).divisors with d ≤ Q / k,
      BombieriVinogradov.reducedThetaError x (d * k) (negativeResidue h (d * k))) ≤
      ∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d (negativeResidue h d) := by
    calc
      _ = ∑ k ∈ K, ∑ d ∈ (∏ p ∈ P, p).divisors with d * k ≤ Q,
          BombieriVinogradov.reducedThetaError x (d * k) (negativeResidue h (d * k)) := by
        apply sum_congr rfl
        intro k hk
        simp only [Nat.le_div_iff_mul_le (hK k hk).pos]
      _ ≤ _ := sum_middlePrime_errors_le P K hP hK hsep Q _
        (fun d => BombieriVinogradov.reducedThetaError_nonneg x d (negativeResidue h d))
  have hu := Finset.sum_le_sum hupper
  rw [sum_add_distrib] at hu
  exact ⟨hlower, hu.trans (_root_.add_le_add le_rfl herr)⟩

/-- BV supplies both translated logarithmic sieve bounds uniformly in
the shift and all chosen prime sets and levels. The theorem assumes
only the separately defined BV statement. -/
theorem eventually_primeShift_rosser_main_and_correction
    (hBV : BombieriVinogradov.Statement) (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∀ h Q : ℕ,
        (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ B →
        ∀ P K : Finset ℕ, (∀ p ∈ P, Nat.Prime p) → (∀ p ∈ P, 2 < p) →
        (∀ k ∈ K, Nat.Prime k) → (∀ p ∈ P, ∀ k ∈ K, p < k) →
        h.Coprime (∏ p ∈ P, p) → (∀ k ∈ K, h.Coprime k) →
        ∀ z : ℕ, (∀ p ∈ P, p < z) → ∀ D : ℝ, 1 < D → D ≤ Q →
        ∀ DAt : ℕ → ℝ, (∀ k ∈ K, 1 < DAt k) →
        (∀ k ∈ K, DAt k ≤ (Q / k : ℕ)) →
          (x : ℝ) * rosserEval P primeDensity z false D -
              C * x / Real.log x ^ A ≤ primeShiftSiftedSum h x P ∧
            (∑ k ∈ K, primeShiftSiftedSumAt h x k P) ≤
              (∑ k ∈ K, ((x : ℝ) / Nat.totient k) *
                rosserEval P primeDensity z true (DAt k)) + C * x / Real.log x ^ A := by
  obtain ⟨B, C, hB, hC, herr⟩ := BombieriVinogradov.thetaStatement_reduced_errors
    (BombieriVinogradov.thetaStatement_of_statement hBV) A hA
  refine ⟨B, C, hB, hC, ?_⟩
  filter_upwards [herr] with x hx
  intro h Q hQ P K hP hodd hK hsep hcopP hcopK z hz D hD hDQ DAt hDAt hDAtQ
  obtain ⟨hlower, hupper⟩ := primeShift_rosser_main_and_correction h x P K
    hP hodd hK hsep hcopP hcopK z hz Q D hD hDQ DAt hDAt hDAtQ
  have he := hx Q hQ (negativeResidue h)
  exact ⟨(sub_le_sub_left he _).trans hlower,
    hupper.trans (_root_.add_le_add le_rfl he)⟩

end Chen.LinearSieve
