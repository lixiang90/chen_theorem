import ChenTheorem.Lemma8.PrimeReciprocal

open Filter Real
open scoped Classical

namespace Chen

/-!
# Lemma 9: Richert--Bombieri input

Chen's proof of Lemma 9 is not self-contained: equation (26) invokes
Theorem A of Richert [11], including formulas (2.18), (2.19), (3.24), and
(4.18), and uses Bombieri's averaged prime-progression theorem [9].  Neither
external theorem is currently available in Mathlib 4.32.2.

The declaration below records exactly their combined specialization after
the two applications displayed in the scan.  It is deliberately named as a
trust-boundary input.  The change of variables, equation (27), loss
management, and the numerical constant `2.6408` are proved in Lean in
`MainEstimates.lean` and `Main/NumericalBounds.lean`.
-/

/-- Combined specialization of Richert's weighted sieve Theorem A and the
Bombieri--Vinogradov averaged progression estimate, corresponding to (25)
and (26) in Chen's paper. -/
axiom eventually_richert_bombieri_equation26
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, Even x →
      (8 - δ) * ((x : ℝ) * chenConst x / (Real.log x) ^ 2) *
          (Real.log 4 - Real.log 8 / 2 + equation27Integral) ≤
        (sievedPrimeCount x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (sievedPrimeCountAt x p' : ℝ)

end Chen
