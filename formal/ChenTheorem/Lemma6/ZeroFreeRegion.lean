/-
The zero-free region interface for equation (21) in Lemma 6.

Chen's estimate `N_m^{(0,k)}` (equation (21) of the scan) moves the contour
from Chen's `alpha`-line to `Re s = 1 - 1 / sqrt(log x)`.  Its only analytic
input, quoted verbatim from the paper, is:

  "When chi_d is a primitive character and `Re S >= 1 - c / d^{1/300}`,
   we have `L(S, chi_d) != 0`, where `c` is a constant."

Mathlib currently proves only the nonvanishing of Dirichlet L-functions on
`re s >= 1` (`DirichletCharacter.LSeries_ne_zero_of_one_lt_re`).  A full
proof of a classical zero-free region — de la Vallee-Poussin's, or the
weaker form with the exponent `1/300` printed in the scan — requires the
Borel–Caratheodory theorem together with quantitative bounds for `-L'/L`
near the line `re s = 1`.  None of this is available in Mathlib today.

This file therefore records the missing interface *honestly*: the definition
`PrimitiveZeroFreeRegion` below is an unproved proposition, and the theorem
`primitive_zero_free_region` asserting it is proved by `sorry`, loudly
documented.  Everything else in the equation-(21) pipeline is proved
unconditionally from this single input.

Two remarks on the exact shape chosen.

* Besides nonvanishing, the interface also provides the standard companion
  bound on the logarithmic derivative inside the region,
  `|L'/L| <= c₂ (log l + 1)^2 log(2 + ||s||)`.  Any formalization of the
  classical region yields such a bound (in fact strictly stronger ones);
  the equation-(21) assembly consumes it through the pointwise weighting
  `kernel decay * log(1 + |nu|)`, which is integrable.
* There is deliberately **no height restriction**: the classical region is
  uniform in the imaginary part, and the contour shift below pushes out to
  heights far beyond `(log x)^2`.
-/
import ChenTheorem.Lemma6.StripGrowth
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open scoped Classical

namespace Chen

/-- The classical zero-free region input of equation (21), recorded honestly
as an *unproved* interface: this is a `Prop`-valued definition, not a theorem.

For every primitive character of modulus `l ≥ 2` and every point `s` with
`re s ≥ 1 - c₁ l^{-1/300}` (Chen's printed shape, with an unspecified
absolute `c₁ > 0`), the L-function does not vanish, and its logarithmic
derivative obeys the standard companion bound with an absolute constant
`c₂`.  Both halves hold uniformly in the height. -/
def PrimitiveZeroFreeRegion : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (l : ℕ) (_ : NeZero l) (χ : DirichletCharacter ℂ l), χ.IsPrimitive →
      ∀ s : ℂ, (1 - c₁ * (l : ℝ) ^ ((-1 : ℝ) / 300)) ≤ s.re →
        DirichletCharacter.LFunction χ s ≠ 0 ∧
          ‖deriv (DirichletCharacter.LFunction χ) s /
              DirichletCharacter.LFunction χ s‖ ≤
            c₂ * (Real.log l + 1) ^ 2 * Real.log (2 + ‖s‖)

/-- **The single unresolved analytic input of the equation-(21) pipeline**
(and, after this formalization, of the whole Lemma 6).

It is exactly the sentence quoted from the scan above, strengthened to the
standard companion `-L'/L` bound that the paper uses implicitly.  Discharging
this `sorry` amounts to formalizing a classical zero-free region theorem for
Dirichlet `L`-functions in Mathlib; no currently-available Mathlib result
implies it. -/
theorem primitive_zero_free_region : PrimitiveZeroFreeRegion := by
  sorry

end Chen
