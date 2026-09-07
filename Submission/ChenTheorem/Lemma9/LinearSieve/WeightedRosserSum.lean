import Submission.ChenTheorem.Lemma9.LinearSieve.PowerRosserBounds

set_option autoImplicit true
open Filter Finset
open scoped Classical

namespace Chen.LinearSieve

theorem upperSieveMidPrimeSum_nonneg (a : ℝ) (ha : 29 / 60 < a) (x : ℕ) (hx : 2 ≤ x) :
    0 ≤ upperSieveMidPrimeSum a x := by
  apply sum_nonneg
  intro p hp
  have hp' := (mem_filter.mp hp).2
  exact div_nonneg (upperSievePrimeWeight_bounds a x p ha
    (by exact_mod_cast (show 1 < x by omega)) ⟨hp'.2.1.le, hp'.2.2⟩).1 (Nat.cast_nonneg _)

/-- Summing all child polynomials costs only a multiplicative error in the
proved totient-weighted prime sum. The assertion applies to any reduced
subset of Chen's middle primes and any set of odd sieving primes. -/
theorem eventually_weighted_rosser_child_sum (a ε : ℝ) (ha : 29 / 60 < a)
    (ha' : a < 1 / 2) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ P : Finset ℕ,
      (∀ q ∈ P, q.Prime) → (∀ q ∈ P, 2 < q) →
      ∀ S : Finset ℕ, S ⊆ midPrimes x →
      (∑ p ∈ S, ((x : ℝ) / Nat.totient p) *
        rosserEval P primeDensity (powerSieveCutoff (1 / 10) x + 1) true
          (powerSieveCutoff a x / p : ℕ)) ≤
      (x : ℝ) * sieveProduct P primeDensity (powerSieveCutoff (1 / 10) x + 1) *
        (1 + ε) * upperSieveMidPrimeSum a x := by
  filter_upwards [eventually_rosser_upper_child_power a ε ha ha' hε,
    eventually_ge_atTop (2 : ℕ)] with x hb hx
  intro P hP hodd S hS
  have hV := (primeDensity_sieveProduct_pos P hP hodd
    (powerSieveCutoff (1 / 10) x + 1)).le
  have hweight (p : ℕ) (hp : p ∈ midPrimes x) : 1 ≤ upperSievePrimeWeight a x p := by
    have hp' := (mem_filter.mp hp).2
    apply upperLinearSieveFunction_ge_one
    linarith [upperSievePrimeWeight_argument a x p ha
      (by exact_mod_cast (show 1 < x by omega)) ⟨hp'.2.1.le, hp'.2.2⟩]
  calc
    _ ≤ ∑ p ∈ S, ((x : ℝ) / Nat.totient p) *
        (sieveProduct P primeDensity (powerSieveCutoff (1 / 10) x + 1) *
          ((1 + ε) * upperSievePrimeWeight a x p)) := by
      apply sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (hb p (hS hp) P hP hodd).trans
      apply mul_le_mul_of_nonneg_left _ hV
      nlinarith [hweight p (hS hp)]
    _ = (x : ℝ) * sieveProduct P primeDensity (powerSieveCutoff (1 / 10) x + 1) *
        (1 + ε) * (∑ p ∈ S, upperSievePrimeWeight a x p / Nat.totient p) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (Nat.cast_nonneg x) hV) (by linarith))
      exact sum_le_sum_of_subset_of_nonneg hS (fun p hp _ =>
        div_nonneg (by linarith [hweight p hp]) (Nat.cast_nonneg _))

end Chen.LinearSieve
