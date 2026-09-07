import ChenTheorem.Lemma8.PrimeReciprocal
import ChenTheorem.Main.ShiftedDefs
import ChenTheorem.Lemma9.LinearSieve.CountCutoff
import ChenTheorem.Lemma9.LinearSieve.ChenSieveNormalization
import ChenTheorem.Lemma9.LinearSieve.PowerSieveLevel
import ChenTheorem.Lemma9.LinearSieve.ShiftedCountAsymptoticSieve
import ChenTheorem.Lemma9.LinearSieve.RosserDepthRecursion
import ChenTheorem.Lemma9.LinearSieve.RosserGrowingTail
import ChenTheorem.Lemma9.LinearSieve.RosserPartialComparison
import ChenTheorem.Lemma9.LinearSieve.AuxiliaryStrictContraction
import ChenTheorem.Lemma9.LinearSieve.AuxiliaryExponentialLowerBound
import ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryLowerBound
import ChenTheorem.Lemma9.LinearSieve.AuxiliaryInflationDerivative
import ChenTheorem.Lemma9.LinearSieve.RosserAuxiliaryComparison
import ChenTheorem.Lemma9.LinearSieve.RosserGrowingParameter
import ChenTheorem.Lemma9.LinearSieve.RosserGrowingPrefix
import ChenTheorem.Lemma9.LinearSieve.AuxiliaryExponentialDecay
import ChenTheorem.Lemma9.LinearSieve.AuxiliaryShiftComparison
import ChenTheorem.Lemma9.LinearSieve.AuxiliaryLogarithmicLower
import ChenTheorem.Lemma9.LinearSieve.AuxiliaryUniformShift
import ChenTheorem.Lemma9.LinearSieve.RosserParentPrefix
import ChenTheorem.Lemma9.LinearSieve.InflatedPrimeWeight
import ChenTheorem.Lemma9.LinearSieve.InflatedAuxiliaryChildSum
import ChenTheorem.Lemma9.LinearSieve.InflatedContractedChildSum
import ChenTheorem.Lemma9.LinearSieve.RosserInflatedParentStep
import ChenTheorem.Lemma9.LinearSieve.RosserFullDefectStep
import ChenTheorem.Lemma9.LinearSieve.RosserBoundedLevel
import ChenTheorem.Lemma9.LinearSieve.RosserAsymptoticError
import ChenTheorem.Lemma9.LinearSieve.CalibratedRosserBounds
import ChenTheorem.Lemma9.LinearSieve.ProfileContinuity
import ChenTheorem.Lemma9.LinearSieve.CountProfileBounds
import ChenTheorem.Lemma9.BombieriVinogradov.FinalEstimate

open Filter Real
open scoped Classical

namespace Chen

/-!
# Lemma 9: proved Richert--Bombieri specialization

Equation (26) follows from the finite Rosser sieve, its uniformly controlled
continuous limits, the calibrated constant `2 exp gamma`, Mertens prime
summation, and the Bombieri--Vinogradov progression estimate. Both the
original Goldbach family and the fixed-shift family are covered below.

The sieve specialization introduces no axiom. The unconditional BV theorem
uses the locally proved primitive zero-free region, including Siegel's bound.
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

open LinearSieve in
/-- Equation (26), obtained by choosing a power level below the square root
whose continuous profile exceeds the requested constant, then applying
the proved count bounds. -/
theorem richert_bombieri_equation26
    (problem : RichertBombieriParameter)
    (hproblem : problem.Admissible) :
    RichertBombieriEquation26 problem := by
  intro δ hδ
  obtain ⟨a, ha, ha', hprofile⟩ := exists_chenContinuousSieveProfile_relative_loss δ hδ
  cases problem with
  | original =>
      filter_upwards [eventually_chen_count_profile_lower BombieriVinogradov.bombieriVinogradov
        a _ ha ha' hprofile, eventually_ge_atTop (3 : ℕ)] with x hc hx
      intro heven
      have hnp : ¬x.Prime := by
        intro hp
        have := hp.even_iff.mp heven
        omega
      simpa only [richertBombieriConstant, richertBombieriCount, richertBombieriCountAt,
        mul_right_comm] using hc hnp
  | shifted h =>
      have hh : h ≠ 0 := (show 0 < h from hproblem.1).ne'
      filter_upwards [eventually_shifted_chen_count_profile_lower BombieriVinogradov.bombieriVinogradov
        h hh a _ ha ha' hprofile] with x hc
      intro _
      simpa only [richertBombieriConstant, richertBombieriCount, richertBombieriCountAt,
        mul_right_comm] using hc

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
