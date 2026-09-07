import Submission.ChenTheorem.Lemma9.LinearSieve.CountLossAsymptotics
import Submission.ChenTheorem.Lemma9.LinearSieve.ChenSieveNormalization

set_option autoImplicit true
open Filter Finset
open scoped Classical

namespace Chen.LinearSieve

/-- BV and all finite count-conversion errors, assembled for Chen's
actual ordinary counts. The only remaining sieve estimates in this
interface concern the two explicit Rosser main terms. -/
theorem eventually_chen_count_lower_of_rosser_polynomials
    (hBV : BombieriVinogradov.Statement) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ x : ℕ in atTop, ¬x.Prime → ∀ Q : ℕ,
        (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ B →
        ∀ D : ℝ, 1 < D → D ≤ Q → ∀ DAt : ℕ → ℝ,
        (∀ k ∈ chenReducedMidPrimes x, 1 < DAt k) →
        (∀ k ∈ chenReducedMidPrimes x, DAt k ≤ (Q / k : ℕ)) →
          (x : ℝ) * rosserEval (chenReducedSmallPrimes x) primeDensity
              (powerSieveCutoff ((1 : ℝ) / 10) x + 1) false D / Real.log x -
            (1 / 2) * ((∑ k ∈ chenReducedMidPrimes x,
              ((x : ℝ) / Nat.totient k) * rosserEval (chenReducedSmallPrimes x)
                primeDensity (powerSieveCutoff ((1 : ℝ) / 10) x + 1) true (DAt k)) /
                  Real.log (countCutoff x)) -
            δ * ((x : ℝ) * chenConst x / Real.log x ^ 2) ≤
          (sievedPrimeCount x : ℝ) -
            (1 / 2) * ∑ k ∈ midPrimes x, (sievedPrimeCountAt x k : ℝ) := by
  obtain ⟨B, C, hB, hC, herror⟩ := BombieriVinogradov.thetaStatement_reduced_errors
    (BombieriVinogradov.thetaStatement_of_statement hBV) 3 (by norm_num)
  refine ⟨B, hB, ?_⟩
  filter_upwards [herror, eventually_count_conversion_error_le C hC.le δ hδ,
    eventually_ge_atTop (2 : ℕ)] with x herr hloss hx
  intro hxnp Q hQ D hD hDQ DAt hDAt hDAtQ
  have hz : ∀ p ∈ chenReducedSmallPrimes x,
      p < powerSieveCutoff ((1 : ℝ) / 10) x + 1 := by
    intro p hp
    have hpS := (mem_filter.mp hp).1
    rw [chenSmallPrimes_eq_oddPrimesLE x (by omega)] at hpS
    have := (Nat.mem_primesLE.mp (mem_filter.mp hpS).1).1
    omega
  have he := herr Q hQ (fun _ => x)
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at he
  have hl := hloss.2 _ he
  have hfinite := chen_count_lower_of_rosser_polynomials x (by omega) hxnp
    (countCutoff x) hloss.1 _ hz Q D hD hDQ DAt hDAt hDAtQ
  simp only [sub_div, add_div] at hfinite
  linarith

end Chen.LinearSieve
