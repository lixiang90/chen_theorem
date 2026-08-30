import ChenTheorem.Lemma7.Normalization

open Filter Real
open scoped Classical

namespace Chen

/-!
# Lemma 7: prime-number-theorem input

The final sentence of the paper's proof of Lemma 7 replaces the smoothed
von Mangoldt sum by its main term.  This is a uniform form of the prime
number theorem: the quotient `x / (p₁ p₂)` is at least `x^(1/3)` throughout
`chenPairs x`, so the ordinary `o(y)` remainder is uniform over all pairs.

Mathlib 4.32.2 does not yet contain the prime number theorem.  We therefore
record that classical theorem as a named trust-boundary input, at the
pointwise strength actually used below.  Everything after this declaration,
including the summation over pairs and all of Chen's constants, is proved in
Lean.
-/

/-- Uniform smoothed prime number theorem on the range of Chen prime pairs.

This is the formal analytic content of the phrase "by Lemma 1" in the last
line of the proof of Lemma 7, together with the classical prime number
theorem for `∑_{n ≤ y} Λ(n)`. -/
axiom eventually_smoothed_pair_mass_le
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℕ in atTop,
      ∀ q ∈ chenPairs x,
        ∑ n ∈ smoothedMIndices x q, smoothedMKernel x q n ≤
          (1 + η) * (x : ℝ) *
            ((q.1 : ℝ) * (q.2 : ℝ) *
              Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹

/-- The smoothed prime mass is nonnegative. -/
theorem smoothedPrimeMass_nonneg {x : ℕ} (hx : 1 < x) :
    0 ≤ smoothedPrimeMass x := by
  unfold smoothedPrimeMass
  apply Finset.sum_nonneg
  intro q hq
  apply Finset.sum_nonneg
  intro n hn
  exact smoothedMKernel_nonneg hx hq

/-- Summing the uniform smoothed PNT over the admissible prime pairs. -/
theorem eventually_smoothedPrimeMass_le
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℕ in atTop,
      smoothedPrimeMass x ≤
        (1 + η) * (x : ℝ) *
          ∑ q ∈ chenPairs x,
            ((q.1 : ℝ) * (q.2 : ℝ) *
              Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ := by
  filter_upwards [eventually_smoothed_pair_mass_le η hη] with x hx
  rw [smoothedPrimeMass]
  calc
    ∑ q ∈ chenPairs x,
        ∑ n ∈ smoothedMIndices x q, smoothedMKernel x q n ≤
      ∑ q ∈ chenPairs x,
        (1 + η) * (x : ℝ) *
          ((q.1 : ℝ) * (q.2 : ℝ) *
            Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ := by
      exact Finset.sum_le_sum fun q hq => hx q hq
    _ = (1 + η) * (x : ℝ) *
        ∑ q ∈ chenPairs x,
          ((q.1 : ℝ) * (q.2 : ℝ) *
            Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ := by
      rw [Finset.mul_sum]

end Chen
