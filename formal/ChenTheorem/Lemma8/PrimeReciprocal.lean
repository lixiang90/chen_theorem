import ChenTheorem.Lemma7.PrimeNumberTheorem
import ChenTheorem.Main.NumericalBounds

open Filter Real
open scoped Classical

namespace Chen

/-!
# Lemma 8: prime-reciprocal partial summation

Between equations (23) and (24), Chen twice replaces a sum over primes by a
Stieltjes integral.  The required analytic fact is the Mertens theorem for
prime reciprocals, uniformly on fixed power intervals.  Mathlib 4.32.2 does
not yet provide this theorem, so the precise multiplicative-error statement
used by the paper is isolated below as a named trust-boundary input.

The conversion from multiplicative error to the additive `δ` formulation of
`chenPairs_kernel_le_integral`, and the complete numerical estimate (24), are
proved in Lean.
-/

/-- The two prime-reciprocal partial-summation steps between (23) and (24).

Here `η` absorbs both occurrences of the paper's factor `1 + ε`; allowing an
arbitrary positive `η` is the invariant asymptotic content of those steps. -/
axiom eventually_chenPairs_kernel_le_one_add_mul_integral
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℕ in atTop,
      ∑ q ∈ chenPairs x,
          ((q.1 : ℝ) * (q.2 : ℝ) *
            Real.log ((x : ℝ) / ((q.1 : ℝ) * q.2)))⁻¹ ≤
        (1 + η) * equation24Integral / Real.log x

end Chen
