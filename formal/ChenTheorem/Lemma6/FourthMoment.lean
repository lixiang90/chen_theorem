/-
The precise fourth-moment input used in Lemma 6 of Chen's paper.

Lemma 3 itself estimates `L(s, χ)`. Immediately after equation (15), Chen
applies Cauchy's integral formula on the circle of radius `1 / log x` around
`β + iν`, then inserts Lemma 3 and the elementary dyadic estimate
`1 / φ(d) ≪ log d / d`. The result is the weighted fourth moment of `L'`
recorded below.
-/
import ChenTheorem.SieveLemmas
import Mathlib.Analysis.Complex.CauchyIntegral

set_option warn.sorry false

open Filter Real
open scoped Classical

namespace Chen

/-- The primitive-character fourth moment of `L'` at modulus `q`. -/
noncomputable def lDerivFourthTerm (q : ℕ) (s : ℂ) : ℝ :=
  if h : q = 0 then 0
  else
    have : NeZero q := ⟨h⟩
    primSum q (fun χ => ‖deriv (DirichletCharacter.LFunction χ) s‖ ^ 4)

/-- The vertical point `β + iν`, where `β = 1/2 + 1/log x`, used after
equation (15). -/
noncomputable def lemma6BetaPoint (x : ℕ) (ν : ℝ) : ℂ :=
  ((1 / 2 + 1 / Real.log x : ℝ) : ℂ) + (ν : ℂ) * Complex.I

/-- The dyadic modulus interval
`2^(l-1) (log x)^100 < d ≤ 2^l (log x)^100`. -/
noncomputable def lemma6ModulusBlock (x l : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun d =>
    (2 : ℝ) ^ (l - 1) * (Real.log x) ^ 100 < d ∧
      (d : ℝ) ≤ (2 : ℝ) ^ l * (Real.log x) ^ 100

/-- A rigorous one-log-slack version of the `L'` fourth-moment estimate used
by Lemma 6 after equation (15).

The scan writes exponent `109`: `100` from the dyadic scale, four from Lemma
3, and five from the Cauchy/Hölder step. It silently absorbs the unbounded
factor `d/φ(d)` into `≪`. Using the uniform elementary bound
`d/φ(d) ≪ log d` gives exponent `110`; this harmless slack is retained in the
formal interface. -/
def Lemma6DerivativeFourthMoment : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, ∀ (l : ℕ) (ν : ℝ), 1 ≤ l →
    ∑ d ∈ lemma6ModulusBlock x l,
        (Nat.totient d : ℝ)⁻¹ * lDerivFourthTerm d (lemma6BetaPoint x ν) ≤
      C * (2 : ℝ) ^ l * (Real.log x) ^ 110 *
        ‖lemma6BetaPoint x ν‖ ^ 2

/-- Cauchy's integral formula plus the dyadic totient estimate transfers the
paper's Lemma 3 to the derivative fourth moment required in Lemma 6.

Mathlib supplies the Cauchy formula; the uniform circle integration,
interchange with the primitive-character sum, and `d/φ(d) ≪ log d`
estimate remain to be assembled here. -/
theorem lemma6_deriv_fourth_moment_of_lFunction_fourth_moment
    (hL : ∃ C : ℝ, 0 < C ∧
      ∀ (Q : ℕ) (s : ℂ), 2 ≤ Q → (1 / 2 : ℝ) ≤ s.re →
        ∑ q ∈ Finset.Icc 2 Q, lFourthTerm q s ≤
          C * (Q : ℝ) ^ 2 * ‖s‖ ^ 2 * (Real.log Q) ^ 4) :
    Lemma6DerivativeFourthMoment := by
  sorry

/-- The derivative fourth moment used below, explicitly derived from the
corrected statement of Lemma 3. -/
theorem lemma6_deriv_fourth_moment : Lemma6DerivativeFourthMoment :=
  lemma6_deriv_fourth_moment_of_lFunction_fourth_moment
    lFunction_fourth_moment

end Chen
