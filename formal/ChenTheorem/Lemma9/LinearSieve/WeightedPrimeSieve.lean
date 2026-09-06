import ChenTheorem.Lemma9.LinearSieve.MiddlePrimeErrors

open Finset
open scoped Classical

namespace Chen.LinearSieve

/-- The logarithmically weighted counterpart of Chen's main count minus
one half of the middle-prime correction. -/
noncomputable def primeDifferenceWeightedSum (x : ℕ) (P K : Finset ℕ) : ℝ :=
  primeDifferenceSiftedSum x P - (1 / 2) * ∑ k ∈ K, primeDifferenceSiftedSumAt x k P

/-- The finite weighted sieve, with constructed Rosser coefficients and a
single unweighted progression-error sum. All main terms are still the
explicit recursive polynomials; their sharp asymptotics are a separate
mathematical step. -/
theorem primeDifference_rosser_main_and_correction (x : ℕ) (P K : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p)
    (hK : ∀ k ∈ K, Nat.Prime k) (hsep : ∀ p ∈ P, ∀ k ∈ K, p < k)
    (hcopP : x.Coprime (∏ p ∈ P, p)) (hcopK : ∀ k ∈ K, x.Coprime k)
    (z : ℕ) (hz : ∀ p ∈ P, p < z)
    (Q : ℕ) (D : ℝ) (hD : 1 < D) (hDQ : D ≤ Q)
    (DAt : ℕ → ℝ) (hDAt : ∀ k ∈ K, 1 < DAt k)
    (hDAtQ : ∀ k ∈ K, DAt k ≤ (Q / k : ℕ)) :
    (x : ℝ) * rosserEval P primeDensity z false D -
        (∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d x) ≤
        primeDifferenceSiftedSum x P ∧
      (∑ k ∈ K, primeDifferenceSiftedSumAt x k P) ≤
        (∑ k ∈ K, ((x : ℝ) / Nat.totient k) * rosserEval P primeDensity z true (DAt k)) +
        (∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d x) := by
  have hlower := (primeDifference_rosser_bounds x P hP hodd hcopP z hz D hD Q hDQ).1
  have hupper (k : ℕ) (hk : k ∈ K) :=
    (primeDifferenceSubsequence_rosser_bounds x k P hP hodd
      (hcopP.mul_right (hcopK k hk))
      (show k.Coprime (∏ p ∈ P, p) from Nat.coprime_prod_right_iff.mpr (fun p hp =>
        (Nat.coprime_primes (hK k hk) (hP p hp)).mpr (ne_of_gt (hsep p hp k hk))))
      z hz (DAt k) (hDAt k hk) (Q / k) (hDAtQ k hk)).2
  have herr : (∑ k ∈ K, ∑ d ∈ (∏ p ∈ P, p).divisors with d ≤ Q / k,
      BombieriVinogradov.reducedThetaError x (d * k) x) ≤
      ∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d x := by
    calc
      _ = ∑ k ∈ K, ∑ d ∈ (∏ p ∈ P, p).divisors with d * k ≤ Q,
          BombieriVinogradov.reducedThetaError x (d * k) x := by
        apply sum_congr rfl
        intro k hk
        simp only [Nat.le_div_iff_mul_le (hK k hk).pos]
      _ ≤ _ := sum_middlePrime_errors_le P K hP hK hsep Q _
        (fun d => BombieriVinogradov.reducedThetaError_nonneg x d x)
  have hu := Finset.sum_le_sum hupper
  rw [sum_add_distrib] at hu
  have hu' := hu.trans (_root_.add_le_add le_rfl herr)
  exact ⟨hlower, hu'⟩

/-- Combining the separate main and correction bounds with Chen's factor
one half gives an error constant of three halves. -/
theorem primeDifference_weighted_rosser_lower (x : ℕ) (P K : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hodd : ∀ p ∈ P, 2 < p)
    (hK : ∀ k ∈ K, Nat.Prime k) (hsep : ∀ p ∈ P, ∀ k ∈ K, p < k)
    (hcopP : x.Coprime (∏ p ∈ P, p)) (hcopK : ∀ k ∈ K, x.Coprime k)
    (z : ℕ) (hz : ∀ p ∈ P, p < z)
    (Q : ℕ) (D : ℝ) (hD : 1 < D) (hDQ : D ≤ Q)
    (DAt : ℕ → ℝ) (hDAt : ∀ k ∈ K, 1 < DAt k)
    (hDAtQ : ∀ k ∈ K, DAt k ≤ (Q / k : ℕ)) :
    (x : ℝ) * rosserEval P primeDensity z false D -
        (1 / 2) * (∑ k ∈ K,
          ((x : ℝ) / Nat.totient k) * rosserEval P primeDensity z true (DAt k)) -
        (3 / 2) * (∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d x) ≤
      primeDifferenceWeightedSum x P K := by
  obtain ⟨hlower, hupper⟩ := primeDifference_rosser_main_and_correction x P K hP hodd hK hsep
    hcopP hcopK z hz Q D hD hDQ DAt hDAt hDAtQ
  unfold primeDifferenceWeightedSum
  linarith

open Filter in
/-- Uniform BV remainder control for the actual weighted prime sieve.
This theorem makes the analytic distribution input and the finite sieve
construction meet, without assuming the desired linear-sieve asymptotic. -/
theorem eventually_primeDifference_weighted_rosser_lower
    (hBV : BombieriVinogradov.Statement) (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∀ Q : ℕ,
        (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B →
        ∀ P K : Finset ℕ, (∀ p ∈ P, Nat.Prime p) → (∀ p ∈ P, 2 < p) →
        (∀ k ∈ K, Nat.Prime k) → (∀ p ∈ P, ∀ k ∈ K, p < k) →
        x.Coprime (∏ p ∈ P, p) → (∀ k ∈ K, x.Coprime k) →
        ∀ z : ℕ, (∀ p ∈ P, p < z) → ∀ D : ℝ, 1 < D → D ≤ Q →
        ∀ DAt : ℕ → ℝ, (∀ k ∈ K, 1 < DAt k) →
        (∀ k ∈ K, DAt k ≤ (Q / k : ℕ)) →
          (x : ℝ) * rosserEval P primeDensity z false D -
              (1 / 2) * (∑ k ∈ K,
                ((x : ℝ) / Nat.totient k) * rosserEval P primeDensity z true (DAt k)) -
              C * x / (Real.log x) ^ A ≤ primeDifferenceWeightedSum x P K := by
  obtain ⟨B, C, hB, hC, herr⟩ := BombieriVinogradov.thetaStatement_reduced_errors
    (BombieriVinogradov.thetaStatement_of_statement hBV) A hA
  refine ⟨B, (3 / 2) * C, hB, by positivity, ?_⟩
  filter_upwards [herr] with x hx
  intro Q hQ P K hP hodd hK hsep hcopP hcopK z hz D hD hDQ DAt hDAt hDAtQ
  have hfinite := primeDifference_weighted_rosser_lower x P K hP hodd hK hsep
    hcopP hcopK z hz Q D hD hDQ DAt hDAt hDAtQ
  have he := hx Q hQ (fun _ => x)
  have he' : (3 / 2) * (∑ d ∈ Icc 1 Q, BombieriVinogradov.reducedThetaError x d x) ≤
      ((3 / 2) * C) * x / (Real.log x) ^ A := by
    calc
      _ ≤ (3 / 2) * (C * x / (Real.log x) ^ A) :=
        mul_le_mul_of_nonneg_left he (by norm_num)
      _ = _ := by ring
  exact (sub_le_sub_left he' _).trans hfinite

end Chen.LinearSieve
