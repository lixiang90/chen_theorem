import ChenTheorem.Lemma8.PrimeReciprocal
import ChenTheorem.Main.ShiftedDefs

open Filter Real
open scoped Classical

namespace Chen

/-!
# Lemma 9: parameterized Richert--Bombieri input

Chen's proof of Lemma 9 is not self-contained: equation (26) invokes
Theorem A of Richert [11], including formulas (2.18), (2.19), (3.24), and
(4.18), and uses Bombieri's averaged prime-progression theorem [9].  Neither
external theorem is currently available in Mathlib 4.32.2.

The declaration below records exactly their combined specialization after
the two applications displayed in the scan.  The original Goldbach problem
and the fixed-shift problem are two values of one parameter type, so there is
only one trust-boundary declaration.  The change of variables, equation (27),
loss management, and the numerical constant `2.6408` are proved in Lean in
`MainEstimates.lean` and `Main/NumericalBounds.lean`.
-/

/-- The two sieve families to which Chen applies the same Richert--Bombieri
argument.  `original` has residue `x`; `shifted h` has the fixed residue
`-h`. -/
inductive RichertBombieriParameter where
  | original
  | shifted (h : ℕ)

/-- Arithmetic side conditions on a Richert--Bombieri family.  The original
Goldbach family has no extra parameter condition.  A fixed shift must be
positive and even. -/
def RichertBombieriParameter.Admissible : RichertBombieriParameter → Prop
  | .original => True
  | .shifted h => 0 < h ∧ Even h

/-- The singular-series factor belonging to a parameterized sieve family. -/
noncomputable def richertBombieriConstant
    (problem : RichertBombieriParameter) (x : ℕ) : ℝ :=
  match problem with
  | .original => chenConst x
  | .shifted h => chenConst h

/-- The primary sifted count in the parameterized equation (26). -/
noncomputable def richertBombieriCount
    (problem : RichertBombieriParameter) (x : ℕ) : ℕ :=
  match problem with
  | .original => sievedPrimeCount x
  | .shifted h => shiftedSievedPrimeCount h x

/-- The count with one middle prime fixed in the parameterized equation
(26). -/
noncomputable def richertBombieriCountAt
    (problem : RichertBombieriParameter) (x p' : ℕ) : ℕ :=
  match problem with
  | .original => sievedPrimeCountAt x p'
  | .shifted h => shiftedSievedPrimeCountAt h x p'

/-- The common conclusion of the two Richert--Bombieri specializations. -/
def RichertBombieriEquation26
    (problem : RichertBombieriParameter) : Prop :=
  ∀ (δ : ℝ), 0 < δ →
    ∀ᶠ x : ℕ in atTop, Even x →
      (8 - δ) *
          ((x : ℝ) * richertBombieriConstant problem x /
            (Real.log x) ^ 2) *
          (Real.log 4 - Real.log 8 / 2 + equation27Integral) ≤
        (richertBombieriCount problem x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (richertBombieriCountAt problem x p' : ℝ)

/-- Combined specialization of Richert's weighted sieve Theorem A and the
Bombieri--Vinogradov averaged progression estimate, corresponding to (25)
and (26) in Chen's paper.  This is the sole Richert--Bombieri trust boundary;
both concrete forms below are derived from it. -/
axiom richert_bombieri_equation26
    (problem : RichertBombieriParameter)
    (hproblem : problem.Admissible) :
    RichertBombieriEquation26 problem

/-- Original-variable specialization of the common Richert--Bombieri
interface. -/
theorem eventually_richert_bombieri_equation26
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, Even x →
      (8 - δ) * ((x : ℝ) * chenConst x / (Real.log x) ^ 2) *
          (Real.log 4 - Real.log 8 / 2 + equation27Integral) ≤
        (sievedPrimeCount x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (sievedPrimeCountAt x p' : ℝ) := by
  simpa [RichertBombieriEquation26, richertBombieriConstant,
    richertBombieriCount, richertBombieriCountAt] using
    (richert_bombieri_equation26 .original trivial δ hδ)

/-- Fixed-shift specialization of the common Richert--Bombieri interface. -/
theorem eventually_shifted_richert_bombieri_equation26
    (h : ℕ) (hh0 : 0 < h) (hhEven : Even h)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, Even x →
      (8 - δ) *
          ((x : ℝ) * chenConst h / Real.log (x : ℝ) ^ 2) *
          (Real.log 4 - Real.log 8 / 2 + equation27Integral) ≤
        (shiftedSievedPrimeCount h x : ℝ) -
          (1 / 2) *
            ∑ p' ∈ midPrimes x,
              (shiftedSievedPrimeCountAt h x p' : ℝ) := by
  simpa [RichertBombieriEquation26, richertBombieriConstant,
    richertBombieriCount, richertBombieriCountAt] using
    (richert_bombieri_equation26 (.shifted h) ⟨hh0, hhEven⟩ δ hδ)

end Chen
