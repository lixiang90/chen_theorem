/-
The main results: the key inequality (28) and Theorems 1 and 2 of Chen's paper.

The deduction of Theorem 1 is:
  (28)      `P_x(1,2) ≥ P_x(x, x^{1/10}) - (1/2) ∑ P_x(x, p, x^{1/10}) - Ω/2 - x^{0.91}`
  Lemma 9   lower-bounds the sieve terms by `2.6408 x C_x/(log x)²`,
  Lemma 8   upper-bounds `Ω/2` by `1.9702 x C_x/(log x)²`,
and `2.6408 - 1.9702 = 0.6706 > 0.67`, the term `x^{0.91}` being negligible
against `x C_x/(log x)²` (using `C_x ≥ twinConst > 0`).

All proofs are `sorry`-placeholders; the statements are the formalization targets.
-/
import ChenTheorem.MainEstimates

-- This file is still an explicitly documented collection of formalization targets.
set_option warn.sorry false

open Filter Real
open scoped Classical

namespace Chen

/-- Inequality **(28)** of the paper: every prime counted by
`P_x(x, x^{1/10})` but not by `P_x(1,2)` forces `x - p` to have at least three
prime factors, all `> x^{1/10}`; such `p` are accounted for (with multiplicity)
by `(1/2) ∑ P_x(x, p', x^{1/10}) + Ω/2`, up to `O(x^{0.91})` degenerate cases. -/
theorem key_inequality :
    ∀ᶠ x : ℕ in atTop, Even x →
      (sievedPrimeCount x : ℝ) -
          (1 / 2) * ∑ p' ∈ midPrimes x, (sievedPrimeCountAt x p' : ℝ) -
          (sieveOmega x : ℝ) / 2 - (x : ℝ) ^ (0.91 : ℝ) ≤
        (chenCount x : ℝ) := by
  sorry

/-- **Theorem 1 (quantitative form)**: for all sufficiently large even `x`,
`P_x(1,2) ≥ 0.67 x C_x / (log x)²`.

Follows from `key_inequality`, `sieved_lower_bound` (Lemma 9),
`sieveOmega_le` (Lemma 8), `twinConst_pos` and `twinConst_le_chenConst`:
`2.6408 - 3.9404/2 = 0.6706` and `x^{0.91} = o(x C_x/(log x)²)`. -/
theorem chenCount_lower :
    ∀ᶠ x : ℕ in atTop, Even x →
      0.67 * (x : ℝ) * chenConst x / (Real.log x) ^ 2 ≤ (chenCount x : ℝ) := by
  sorry

/-- **Theorem 1 (qualitative form — Chen's theorem)**: every sufficiently large
even number is the sum of a prime and a number that is either a prime or a
product of two primes. -/
theorem chen_theorem :
    ∀ᶠ x : ℕ in atTop, Even x →
      ∃ p m : ℕ, p.Prime ∧ IsP2 m ∧ p + m = x := by
  sorry

/-- **Theorem 2 (quantitative form)**: for every positive even `h` and all
sufficiently large `x`,
`x_h(1,2) ≥ 0.67 x C_h / (log x)²`.
(The singular series for the shifted problem `p + h` is `C_h`, the product
running over the odd primes dividing `h`.) -/
theorem chenCountShift_lower (h : ℕ) (hh : Even h) (h0 : 0 < h) :
    ∀ᶠ x : ℕ in atTop,
      0.67 * (x : ℝ) * chenConst h / (Real.log x) ^ 2 ≤
        (chenCountShift h x : ℝ) := by
  sorry

/-- **Theorem 2 (qualitative form)**: for every positive even `h` there are
infinitely many primes `p` such that `p + h` has at most two prime factors.
For `h = 2` this is the celebrated approximation to the twin prime conjecture. -/
theorem chen_twin (h : ℕ) (hh : Even h) (h0 : 0 < h) :
    {p : ℕ | p.Prime ∧ IsP2 (p + h)}.Infinite := by
  sorry

end Chen
