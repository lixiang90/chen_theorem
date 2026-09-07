import Submission.ChenTheorem.Lemma9.LinearSieve.ShiftedCountLossAsymptotics
import Submission.ChenTheorem.Lemma9.LinearSieve.ShiftedSieveNormalization
import Submission.ChenTheorem.Lemma9.LinearSieve.PowerSieveLevel

set_option autoImplicit true
open Filter Finset
open scoped Classical

namespace Chen.LinearSieve

/-- The exact shifted ordinary counts bounded by explicit Rosser main
terms, with all arithmetic and count-conversion remainders absorbed. -/
theorem eventually_shifted_chen_count_lower_of_rosser_polynomials
    (hBV : BombieriVinogradov.Statement) (h : ℕ) (hh : h ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ x : ℕ in atTop, ∀ Q : ℕ,
        (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ B →
        ∀ D : ℝ, 1 < D → D ≤ Q → ∀ DAt : ℕ → ℝ,
        (∀ k ∈ chenShiftedMidPrimes h x, 1 < DAt k) →
        (∀ k ∈ chenShiftedMidPrimes h x, DAt k ≤ (Q / k : ℕ)) →
          (x : ℝ) * rosserEval (chenShiftedSmallPrimes h x) primeDensity
              (powerSieveCutoff ((1 : ℝ) / 10) x + 1) false D / Real.log x -
            (1 / 2) * ((∑ k ∈ chenShiftedMidPrimes h x,
              ((x : ℝ) / Nat.totient k) * rosserEval (chenShiftedSmallPrimes h x)
                primeDensity (powerSieveCutoff ((1 : ℝ) / 10) x + 1) true (DAt k)) /
                  Real.log (countCutoff x)) -
            δ * ((x : ℝ) * chenConst h / Real.log x ^ 2) ≤
          (shiftedSievedPrimeCount h x : ℝ) -
            (1 / 2) * ∑ k ∈ midPrimes x, (shiftedSievedPrimeCountAt h x k : ℝ) := by
  obtain ⟨B, C, hB, hC, herror⟩ := BombieriVinogradov.thetaStatement_reduced_errors
    (BombieriVinogradov.thetaStatement_of_statement hBV) 3 (by norm_num)
  refine ⟨B, hB, ?_⟩
  filter_upwards [herror, eventually_shifted_count_conversion_error_le h C hC.le δ hδ,
    eventually_ge_atTop (2 : ℕ)] with x herr hloss hx
  intro Q hQ D hD hDQ DAt hDAt hDAtQ
  have hz : ∀ p ∈ chenShiftedSmallPrimes h x,
      p < powerSieveCutoff ((1 : ℝ) / 10) x + 1 := by
    intro p hp
    have hpS := (mem_filter.mp hp).1
    rw [chenSmallPrimes_eq_oddPrimesLE x (by omega)] at hpS
    have := (Nat.mem_primesLE.mp (mem_filter.mp hpS).1).1
    omega
  have he := herr Q hQ (negativeResidue h)
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at he
  have hl := hloss.2.2 _ he
  have hfinite := shifted_chen_count_lower_of_rosser_polynomials h x hh (by omega)
    (countCutoff x) hloss.1 hloss.2.1 _ hz Q D hD hDQ DAt hDAt hDAtQ
  simp only [sub_div, add_div] at hfinite
  linarith

/-- Concrete power levels complete the finite-sieve and remainder part
of the fixed-shift problem. As in the original-variable theorem, the
sharp linear-sieve estimates for the remaining polynomials are separate. -/
theorem eventually_shifted_chen_count_lower_at_power_level
    (hBV : BombieriVinogradov.Statement) (h : ℕ) (hh : h ≠ 0)
    (a : ℝ) (ha : 1 / 3 < a) (ha' : a < 1 / 2) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * rosserEval (chenShiftedSmallPrimes h x) primeDensity
          (powerSieveCutoff ((1 : ℝ) / 10) x + 1) false (powerSieveCutoff a x) / Real.log x -
        (1 / 2) * ((∑ k ∈ chenShiftedMidPrimes h x,
          ((x : ℝ) / Nat.totient k) * rosserEval (chenShiftedSmallPrimes h x) primeDensity
            (powerSieveCutoff ((1 : ℝ) / 10) x + 1) true (powerSieveCutoff a x / k : ℕ)) /
              Real.log (countCutoff x)) -
        δ * ((x : ℝ) * chenConst h / Real.log x ^ 2) ≤
      (shiftedSievedPrimeCount h x : ℝ) -
        (1 / 2) * ∑ k ∈ midPrimes x, (shiftedSievedPrimeCountAt h x k : ℝ) := by
  obtain ⟨B, hB, hcount⟩ := eventually_shifted_chen_count_lower_of_rosser_polynomials hBV h hh δ hδ
  filter_upwards [hcount, eventually_powerSieveCutoff_le_bv_level a ha' B,
    eventually_powerSieveCutoff_div_midPrime a ha,
    (powerSieveCutoff_tendsto a (by linarith)).eventually (eventually_ge_atTop 2)]
    with x hcount hQ hmid hlevel
  apply hcount (powerSieveCutoff a x) hQ (powerSieveCutoff a x)
    (by exact_mod_cast (show 1 < powerSieveCutoff a x by omega)) le_rfl
    (fun k => (powerSieveCutoff a x / k : ℕ))
  · intro k hk
    exact_mod_cast hmid k (mem_filter.mp hk).1
  · exact fun _ _ => le_rfl

end Chen.LinearSieve
